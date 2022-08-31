/**
 * Copyright 2022 mojo Friedrich Schiller University Jena
 *
 * This file is part of mojo.
 *
 * mojo is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * mojo is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with mojo. If not, see <http://www.gnu.org/licenses/>.
 */
package de.jena.uni.mojo.plan.plugin.loop.decomposition.soundness;

import de.jena.uni.mojo.analysis.edge.Edge;
import de.jena.uni.mojo.analysis.edge.StrongComponentsAnalysis;
import de.jena.uni.mojo.analysis.information.AnalysisInformation;
import de.jena.uni.mojo.error.*;
import de.jena.uni.mojo.model.WGNode;
import de.jena.uni.mojo.model.WorkflowGraph;
import de.jena.uni.mojo.plan.ControlFlowAnalysisPlan;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.LoopDecomposition;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.LoopInformation;
import de.jena.uni.mojo.util.store.ElementStore;

import java.util.*;

/**
 * Class SoundnessLoopDecompositionAnalysis.
 * Extends a loop decomposition by performing a soundness analysis afterwards and modifying the cutoff edges, etc.
 * For more details take a look in:
 * ""
 * @author Dr. Dipl.-Inf. Thomas M. Prinz
 */
public class SoundnessLoopDecompositionAnalysis extends LoopDecomposition {

    /**
     * A serial version UID.
     */
    private static final long serialVersionUID = 7120671292823189427L;

    /**
     * Constructor. This is used for external usage (as entry to the analysis).
     *
     * @param graph    The workflow graph.
     * @param map      The node map.
     * @param reporter The reporter.
     */
    public SoundnessLoopDecompositionAnalysis(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter,
                                              ElementStore store) {
        super(graph, map, reporter);
    }

    /**
     * Constructor. This is used for recursive calls during the analysis.
     * @param graph The workflow graph.
     * @param map The node map.
     * @param reporter The reporter.
     * @param origin The origin workflow graph.
     * @param recursionDepth The recursion depth.
     */
    private SoundnessLoopDecompositionAnalysis(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter,
                                               WorkflowGraph origin, int recursionDepth) {
        super(graph, map, reporter, origin, recursionDepth);
    }

    @Override
    protected List<Annotation> analyze() {
        // Add first put some information, like the file name, in the reporting system to redirect the graph
        // perfectly.
        if (this.origin != this.graph) {
            reporter.put(graph, AnalysisInformation.FILE_NAME, reporter.get(origin, AnalysisInformation.FILE_NAME));
        }
        // Report the recursion depth.
        reporter.put(graph, "RECURSION_DEPTH", recursionDepth);

        // Determine the largest id to assign new ids.
        this.maxId = graph.getNodeSet().size();
        // Determine used ids so that unset ids can be reused.
        this.freeIds = (BitSet) graph.getNodeSet().clone();
        this.freeIds.set(graph.getStart().getId());
        this.freeIds.set(graph.getEnd().getId());

        //
        // Step 1: Perform a strong component analysis and determine the loops.
        //
        StrongComponentsAnalysis strongComponentsAnalysis = new StrongComponentsAnalysis(graph, map, reporter);
        strongComponentsAnalysis.compute();
        ArrayList<BitSet> loops = strongComponentsAnalysis.getComponents();

        //
        // If no cycles were found at all, the workflow graph is acyclic.
        // Perform a soundness analysis on that acyclic graph.
        //
        if (loops.size() == 0) {
            // The soundness analysis from the mojo core.
            ControlFlowAnalysisPlan soundnessAnalysis = new ControlFlowAnalysisPlan(graph, map, reporter);
            errors.addAll(soundnessAnalysis.compute());

            // Add everything if the graph is not the original workflow graph.
            if (origin != graph) {
                for (Annotation error: errors) {
                    this.edgesVisited++;
                    if (error instanceof DeadlockAnnotation) {
                        reporter.add(origin, AnalysisInformation.NUMBER_DEADLOCKS, 1);
                        reporter.add(origin, AnalysisInformation.NUMBER_DEADLOCKS_NORMAL, 1);
                    } else if (error instanceof AbundanceAnnotation) {
                        reporter.add(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION, 1);
                        reporter.add(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_NORMAL, 1);
                    }
                }
            }

            // Add the workflow graph to the list of workflow graphs and return the errors.
            workflowGraphs.add(graph);
            return errors;
        }

        //
        // Cycles found
        //
        WorkflowGraph graph = this.graph;

        //
        // Step 2: Iterate over each loop.
        //
        // Define sets thar are recycled.
        BitSet exitOutgoing = new BitSet(edges.size());
        for (BitSet loop : loops) {
            exitOutgoing.clear();

            // Sets describing the loop in detail.
            BitSet loopIncoming = new BitSet(edges.size());
            BitSet loopOutgoing = new BitSet(edges.size());

            //
            // Step 2.1: Find loop entries and exits
            //
            // Iterate over each edge of the loop.
            for (int e = loop.nextSetBit(0); e >= 0; e = loop.nextSetBit(e + 1)) {
                this.edgesVisited++;
                // Get the edge.
                Edge edge = edges.get(e);

                //
                // Find loop entries (their incoming edges, respectively)
                //
                // Determine the incoming edges of the source node of the current edge.
                BitSet in = incoming[edge.src.getId()];
                // A loop entry has by definition at least two incoming edges (one from inside and one from outside the
                // loop).
                if (in.cardinality() >= 2) {
                    // Determine those incoming edges that are *not* in the loop.
                    BitSet fromOut = (BitSet) in.clone();
                    fromOut.andNot(loop);

                    // If this set is *not* empty, then there are incoming edges from outside the loop.
                    if (!fromOut.isEmpty()) {
                        // edge and e, respectively, are the outgoing edge of a loop entry.
                        // Add the incoming edges to the set of loop incoming edges.
                        loopIncoming.or(fromOut);
                    }
                }

                //
                // Find loop exits (their outgoing edges respectively)
                //
                // Determine the outgoing edges of the target node of the current edge.
                BitSet out = outgoing[edge.tgt.getId()];
                // A loop exit has by definition at least two outgoing edges (one inside the loop and one to outside.
                if (out.cardinality() >= 2) {
                    // Determine those outgoing edges that are *not* in the loop.
                    BitSet toOut = (BitSet) out.clone();
                    toOut.andNot(loop);

                    // If this set is *not* empty, then there are outgoing edges to outside the loop.
                    if (!toOut.isEmpty()) {
                        // edge and e, respectively, are the incoming edge of a loop exit.
                        // Add the outgoing edges to the set of loop outgoing edges.
                        loopOutgoing.or(toOut);
                        exitOutgoing.or(out);
                    }
                }
            }

            //
            // Apply rules described in the above-mentioned paper.
            //
            this.applyRule1(loop, loopOutgoing);
            this.applyRule2(loop, loopIncoming);

            // Create a loop fragment that includes loop outgoing edges.
            BitSet extendedLoop = (BitSet) loop.clone();
            extendedLoop.or(loopOutgoing);

            //
            // Step 2.2: Set cutoff edges as those edges being inner-loop outgoing edges of loop exits.
            //
            BitSet cutoffEdges = (BitSet) exitOutgoing.clone();
            cutoffEdges.andNot(loopOutgoing);

            //
            // Step 2.3: Determine the "do-body" with a depth-first search, i.e., this part remaining in the
            //           workflow graph.
            //
            // This is done by an iterative depth-first search.
            // Define a working list that starts at the loop incoming edges.
            BitSet workingList = (BitSet) loopIncoming.clone();
            BitSet doBody = new BitSet(loopIncoming.size());
            // As long as there are reachable edges in the working list, we perform the search.
            while (!workingList.isEmpty()) {
                // Get the current edge id of the list ...
                int cur = workingList.nextSetBit(0);
                // ... and remove it from the list.
                workingList.clear(cur);
                // Determine the outgoing edges of the current edge's target ...
                BitSet outgoing = (BitSet) this.outgoing[edges.get(cur).tgt.getId()].clone();
                // ... remove the cutoff edges from it ...
                outgoing.andNot(cutoffEdges);
                // ... and already visited edges.
                outgoing.andNot(doBody);
                // Add the remaining outgoing edges as part of the do-body and to the working list.
                doBody.or(outgoing);
                workingList.or(outgoing);
            }

            //
            // Step 2.4: Find the loop fragments
            //
            // We cut the loop by removing all cutoff edges from it.
            BitSet cutLoop = (BitSet) loop.clone();
            cutLoop.andNot(cutoffEdges);
            cutLoop.or(loopOutgoing);

            // Define a set of unvisited edges, being all at the start.
            BitSet unvisited = (BitSet) cutLoop.clone();
            BitSet unvisitedInFragment = new BitSet(unvisited.size());
            BitSet newEdges = new BitSet(unvisited.size());
            // Define a list for storing the loop fragments.
            ArrayList<BitSet> fragments = new ArrayList<>();
            // Idea: Any unvisited edge is taken. From it, in all directions, the graph is visited as long as
            // it does not reach any edge already visited. During this search, all edges belong to the same fragment.
            while (!unvisited.isEmpty()) {
                edgesVisited++;
                // Take the first edge out of it.
                int cur = unvisited.nextSetBit(0);
                unvisited.clear(cur);

                // Create a new fragment that contains the current edge.
                BitSet currentFragment = new BitSet(unvisited.size());
                fragments.add(currentFragment);

                // Reset the unvisited in fragment set.
                unvisitedInFragment.clear();

                // Add the current edge to the fragment and mark it as unvisited.
                currentFragment.set(cur);
                unvisitedInFragment.set(cur);

                // As long as there are unvisited edges, search for the current fragment.
                while (!unvisitedInFragment.isEmpty()) {
                    edgesVisited++;
                    // Take the next unvisited edge out of it.
                    int unvis = unvisitedInFragment.nextSetBit(0);
                    unvisitedInFragment.clear(unvis);
                    // Delete it also from the unvisited edge set.
                    unvisited.clear(unvis);

                    // Get the model edge.
                    Edge current = edges.get(unvis);
                    // Determine the set of all edges that are connected with the current edges' source and target.
                    newEdges.clear();
                    newEdges.or(this.incoming[current.src.getId()]);
                    newEdges.or(this.incoming[current.tgt.getId()]);
                    newEdges.or(this.outgoing[current.src.getId()]);
                    newEdges.or(this.outgoing[current.tgt.getId()]);

                    // We just want to examine those edges within the (extended) loop.
                    newEdges.and(extendedLoop);
                    // We do *not* want to visit cutoff edges.
                    newEdges.andNot(cutoffEdges);
                    // We just want to examine unvisited edges.
                    newEdges.and(unvisited);
                    // The remaining edges are added to the current fragment ...
                    currentFragment.or(newEdges);
                    // ... and have to be examined further.
                    unvisitedInFragment.or(newEdges);
                    unvisitedInFragment.and(unvisited);
                }
            }

            //
            // Step 2.5: Derive all loop fragment workflow graphs
            //
            for (BitSet fragment: fragments) {
                // The loop outgoing edges of the fragment are those of the loop within the fragment.
                BitSet fragLoopOut = (BitSet) loopOutgoing.clone();
                fragLoopOut.and(fragment);
                // The fragment should not contain the loop outgoing edges.
                BitSet withoutLoopOut = (BitSet) fragment.clone();
                withoutLoopOut.andNot(fragLoopOut);
                // Create the loop fragment by recycling the create-iteration-body method.
                WorkflowGraph fragmentWFG =
                        this.createIterationBody(withoutLoopOut, cutoffEdges, fragLoopOut, true);

                // The fragment again is a valid workflow graph and must be considered during soundness analysis.
                // Therefore, loop decomposition with soundness analysis is done recursively.
                SoundnessLoopDecompositionAnalysis loopDecomposition = new SoundnessLoopDecompositionAnalysis(fragmentWFG,
                        this.lastMapIterationBody,
                        reporter,
                        this.graph,
                        this.recursionDepth + 1);
                // All errors, etc., are reported to the current workflow graph.
                errors.addAll(loopDecomposition.compute());
                edgesVisited += loopDecomposition.getEdgesVisited();
                workflowGraphs.addAll(loopDecomposition.getDecomposition());
            }
            // Store information about this loop.
            this.loopInformation.add(new LoopInformation(extendedLoop, doBody, cutoffEdges, loopIncoming,
                    loopOutgoing));
        }

        //
        // Step 3: Reduce the workflow graph to those nodes in the do-bodies.
        //
        graph = this.reduce(graph);

        //
        // Step 4: Perform again a loop decomposition on the reduced workflow graph to find nested loops and finally
        //         perform a soundness analysis on the acyclic graph.
        //
        SoundnessLoopDecompositionAnalysis loopDecomposition = new SoundnessLoopDecompositionAnalysis(graph,
                this.lastMap,
                reporter,
                this.graph,
                this.recursionDepth + 1);
        // Report all errors, etc.,  to the original workflow graph.
        errors.addAll(loopDecomposition.compute());
        edgesVisited += loopDecomposition.getEdgesVisited();
        workflowGraphs.addAll(loopDecomposition.getDecomposition());

        // Report some meta information.
        reporter.put(this.graph, "NUMBER_VISITED_EDGES_DECOMPOSITION", edgesVisited);
        reporter.put(this.graph, "NUMBER_LOOPS", loops.size());
        reporter.put(this.graph, "REDUCED_GRAPH_SIZE_EDGES", graph.getEdges().size());
        reporter.put(this.graph, "REDUCED_GRAPH_SIZE_NODES", graph.getNodeListInclusive().size());

        return errors;
    }

    /**
     * Apply rule 1 that each loop exit is an XOR split.
     * @param loop The loop.
     * @param loopOutgoing The loop outgoing edges.
     */
    private void applyRule1(BitSet loop, BitSet loopOutgoing) {
        loopOutgoing = (BitSet) loopOutgoing.clone();
        // Iterate over each edge that leaves the loop.
        // Their source nodes are loop exits that should be XOR splits.
        for (int o = loopOutgoing.nextSetBit(0); o >= 0; o = loopOutgoing.nextSetBit(o + 1)) {
            this.edgesVisited++;
            // Get the edge ...
            Edge edge = edges.get(o);
            // ... and the loop exit.
            WGNode exit = edge.src;
            // Some loop exits can have multiple outgoing edges outside the loop.
            // We delete them from the set to avoid unnecessary errors.
            loopOutgoing.andNot(this.outgoing[exit.getId()]);
            // If the exit is *not* an XOR split (split in mojo slang) there is an error.
            if (exit.getType() != WGNode.Type.SPLIT) {
                AbundanceCycleAnnotation annotation = new AbundanceCycleAnnotation(this);
                annotation.addInvolvedNode(exit);
                annotation.addOpeningNode(exit);
                annotation.addPathToFailure(loop);

                errors.add(annotation);
                reporter.add(graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_LOOP, 1);
            }
        }
    }

    /**
     * Apply rule 2 that each loop entry is not an AND join.
     * @param loop The loop.
     * @param loopIncoming The loop incoming edges.
     */
    private void applyRule2(BitSet loop, BitSet loopIncoming) {
        loopIncoming = (BitSet) loopIncoming.clone();
        // Iterate over edge that enters the loop.
        // Their target nodes are loop entries that should be OR or XOR joins.
        for (int i = loopIncoming.nextSetBit(0); i >= 0; i = loopIncoming.nextSetBit(i + 1)) {
            this.edgesVisited++;
            // Get the edge ...
            Edge edge = edges.get(i);
            // ... and the loop entry.
            WGNode entry = edge.tgt;
            // Some loop entries can have multiple incoming edges entering the loop.
            // We delete them from the set to avoid unnecessary errors.
            loopIncoming.andNot(this.incoming[entry.getId()]);
            // If the entry is an AND-join (join in mojo slang) there is an error.
            if (entry.getType() == WGNode.Type.JOIN) {
                DeadlockCycleAnnotation annotation = new DeadlockCycleAnnotation(this);
                annotation.addFailureNode(entry);
                annotation.addInvolvedNode(entry);
                annotation.addOpeningNode(entry);
                annotation.addPathToFailure(loop);

                errors.add(annotation);
                reporter.add(graph, AnalysisInformation.NUMBER_DEADLOCKS_LOOP, 1);
            }
        }
    }
}
