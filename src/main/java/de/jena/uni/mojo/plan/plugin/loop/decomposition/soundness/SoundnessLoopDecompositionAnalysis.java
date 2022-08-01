package de.jena.uni.mojo.plan.plugin.loop.decomposition.soundness;

import de.jena.uni.mojo.analysis.edge.Edge;
import de.jena.uni.mojo.analysis.edge.StrongComponentsAnalysis;
import de.jena.uni.mojo.analysis.information.AnalysisInformation;
import de.jena.uni.mojo.error.AbundanceCycleAnnotation;
import de.jena.uni.mojo.error.Annotation;
import de.jena.uni.mojo.error.DeadlockCycleAnnotation;
import de.jena.uni.mojo.model.WGNode;
import de.jena.uni.mojo.model.WorkflowGraph;
import de.jena.uni.mojo.plan.ControlFlowAnalysisPlan;
import de.jena.uni.mojo.plan.WorkflowGraphMajorPlan;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.LoopDecomposition;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.LoopInformation;
import de.jena.uni.mojo.util.store.ElementStore;

import java.util.*;

public class SoundnessLoopDecompositionAnalysis extends LoopDecomposition {

    /**
     * The element store.
     */
    private ElementStore store;

    /**
     * Constructor.
     *
     * @param graph    The workflow graph.
     * @param map      The node map.
     * @param reporter The reporter.
     */
    public SoundnessLoopDecompositionAnalysis(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter,
                                              ElementStore store) {
        super(graph, map, reporter);
        this.store = store;
    }

    /**
     * Constructor.
     * @param graph The workflow graph.
     * @param map The node map.
     * @param reporter The reporter.
     * @param origin The origin workflow graph.
     * @param recursionDepth The recursion depth.
     */
    private SoundnessLoopDecompositionAnalysis(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter, WorkflowGraph origin,
                              int recursionDepth) {
        super(graph, map, reporter, origin, recursionDepth);
    }

    @Override
    protected List<Annotation> analyze() {
        if (this.origin != this.graph) {
            reporter.put(graph, AnalysisInformation.FILE_NAME, reporter.get(origin, AnalysisInformation.FILE_NAME));
        }
        reporter.put(graph, "RECURSION_DEPTH", recursionDepth);
        // Determine the largest id to assign new ids.
        this.maxId = graph.getNodeSet().size();
        this.freeIds = (BitSet) graph.getNodeSet().clone();
        this.freeIds.set(graph.getStart().getId());
        this.freeIds.set(graph.getEnd().getId());

        //
        // Step 1: Perform strong component analysis.
        //
        StrongComponentsAnalysis strongComponentsAnalysis = new StrongComponentsAnalysis(graph, map, reporter);
        strongComponentsAnalysis.compute();
        ArrayList<BitSet> components = strongComponentsAnalysis.getComponents();

        // If no cycles where found at all, the workflow graph is acyclic.
        // Perform a soundness analysis on that acyclic graph.
        if (components.size() == 0) {
            ControlFlowAnalysisPlan soundnessAnalysis = new ControlFlowAnalysisPlan(graph, map, reporter);
            errors.addAll(soundnessAnalysis.compute());

            // Add everything.
            if (origin != graph) {
                Object currentDeadlocks = reporter.get(graph, AnalysisInformation.NUMBER_DEADLOCKS);
                Object currentDeadlocksNormal = reporter.get(graph, AnalysisInformation.NUMBER_DEADLOCKS_NORMAL);
                Object currentDeadlocksLoop = reporter.get(graph, AnalysisInformation.NUMBER_DEADLOCKS_LOOP);
                Object currentLoS = reporter.get(graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION);
                Object currentLoSNormal = reporter.get(graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_NORMAL);
                Object currentLoSLoop = reporter.get(graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_LOOP);

                Object originDeadlocks = reporter.get(origin, AnalysisInformation.NUMBER_DEADLOCKS);
                Object originDeadlocksNormal = reporter.get(origin, AnalysisInformation.NUMBER_DEADLOCKS_NORMAL);
                Object originDeadlocksLoop = reporter.get(origin, AnalysisInformation.NUMBER_DEADLOCKS_LOOP);
                Object originLoS = reporter.get(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION);
                Object originLoSNormal = reporter.get(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_NORMAL);
                Object originLoSLoop = reporter.get(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_LOOP);

                reporter.put(origin, AnalysisInformation.NUMBER_DEADLOCKS,
                        (currentDeadlocks == null ? 0 : (int) currentDeadlocks) +
                                (originDeadlocks == null ? 0 : (int) originDeadlocks));
                reporter.put(origin, AnalysisInformation.NUMBER_DEADLOCKS_NORMAL,
                        (currentDeadlocksNormal == null ? 0 : (int) currentDeadlocksNormal) +
                                (originDeadlocksNormal == null ? 0 : (int) originDeadlocksNormal));
                reporter.put(origin, AnalysisInformation.NUMBER_DEADLOCKS_LOOP,
                        (currentDeadlocksLoop == null ? 0 : (int) currentDeadlocksLoop) +
                                (originDeadlocksLoop == null ? 0 : (int) originDeadlocksLoop));
                reporter.put(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION,
                        (currentLoS == null ? 0 : (int) currentLoS) +
                                (originLoS == null ? 0 : (int) originLoS));
                reporter.put(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_NORMAL,
                        (currentLoSNormal == null ? 0 : (int) currentLoSNormal) +
                                (originLoSNormal == null ? 0 : (int) originLoSNormal));
                reporter.put(origin, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_LOOP,
                        (currentLoSLoop == null ? 0 : (int) currentLoSLoop) +
                                (originLoSLoop == null ? 0 : (int) originLoSLoop));
            }

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
        for (BitSet component : components) {
            BitSet loopIncoming = new BitSet(edges.size());
            BitSet loopOutgoing = new BitSet(edges.size());
            BitSet exitOutgoing = new BitSet(edges.size());
            BitSet cutOutgoing = new BitSet(edges.size());
            BitSet entryIncoming = new BitSet(edges.size());

            //
            // Step 2.1: Find loop entries and exits
            //
            for (int e = component.nextSetBit(0); e >= 0; e = component.nextSetBit(e + 1)) {
                Edge edge = edges.get(e);
                edgesVisited++;

                // Find loop entries
                BitSet in = incoming[edge.src.getId()];
                if (in.cardinality() >= 2) {
                    BitSet fromOut = (BitSet) in.clone();
                    fromOut.andNot(component);
                    if (!fromOut.isEmpty()) {
                        // Loop incoming edges.
                        loopIncoming.or(fromOut);
                        entryIncoming.or(in);
                        entryIncoming.andNot(fromOut);
                    }
                }

                // Find loop exits
                BitSet out = outgoing[edge.tgt.getId()];
                if (out.cardinality() >= 2) {
                    BitSet toOut = (BitSet) out.clone();
                    toOut.andNot(component);
                    if (!toOut.isEmpty()) {
                        // Loop outgoing edges.
                        loopOutgoing.or(toOut);
                        exitOutgoing.or(out);
                        BitSet cutOut = (BitSet) out.clone();
                        cutOut.and(component);
                        cutOutgoing.or(cutOut);
                    }
                }
            }

            // Apply rules
            this.applyRule1(component, loopOutgoing);
            this.applyRule2(component, loopIncoming);

            // Create a SCC that includes loop incoming and outgoing edges.
            BitSet extComponent = (BitSet) component.clone();
            extComponent.or(loopOutgoing);

            //
            // Step 2.2: Find cutoff edges with a modified depth-first search.
            //
            BitSet cutoffEdges = (BitSet) exitOutgoing.clone();
            cutoffEdges.andNot(loopOutgoing);

            //
            // Step 2.3: Determine the do-body with a depth-first search
            //
            BitSet workingList = (BitSet) loopIncoming.clone();
            BitSet doBody = new BitSet(loopIncoming.size());
            while (!workingList.isEmpty()) {
                int cur = workingList.nextSetBit(0);
                workingList.clear(cur);
                BitSet outgoing = (BitSet) this.outgoing[edges.get(cur).tgt.getId()].clone(); // TODO: HERE
                outgoing.andNot(cutoffEdges);
                outgoing.andNot(doBody);
                doBody.or(outgoing);
                workingList.or(outgoing);
            }

            /*System.out.println("Loop");
            System.out.println(component);
            System.out.println(extComponent);
            System.out.println("Do Body");
            System.out.println(doBody);
            System.out.println("Cutoff");
            System.out.println(cutoffEdges);
            System.out.println("Loopout");
            System.out.println(loopOutgoing);*/

            //
            // Step 2.4: Find the loop fragments
            //

            // Remove the cutoff edges from the loop.
            BitSet cutLoop = (BitSet) component.clone(); // TODO: HERE
            cutLoop.andNot(cutoffEdges);
            cutLoop.or(loopOutgoing);

            // All edges not visited yet.
            BitSet unvisited = (BitSet) cutLoop.clone();
            ArrayList<BitSet> fragments = new ArrayList<>();
            while (!unvisited.isEmpty()) {
                edgesVisited++;
                // Take the first edge out of it.
                int cur = unvisited.nextSetBit(0);
                unvisited.clear(cur);

                // Create a new fragment for the current edge.
                BitSet currentFragment = new BitSet(unvisited.size());
                fragments.add(currentFragment);
                BitSet unvisitedInFragment = new BitSet(unvisited.size());

                currentFragment.set(cur);
                unvisitedInFragment.set(cur);

                while (!unvisitedInFragment.isEmpty()) {
                    edgesVisited++;
                    int unvis = unvisitedInFragment.nextSetBit(0);
                    unvisitedInFragment.clear(unvis);
                    unvisited.clear(unvis);

                    // TODO: HERE
                    Edge current = edges.get(unvis);
                    BitSet newEdges = (BitSet) this.incoming[current.src.getId()].clone();
                    newEdges.or(this.incoming[current.tgt.getId()]);
                    newEdges.or(this.outgoing[current.src.getId()]);
                    newEdges.or(this.outgoing[current.tgt.getId()]);

                    newEdges.and(extComponent);
                    newEdges.andNot(cutoffEdges);
                    newEdges.and(unvisited);
                    currentFragment.or(newEdges);
                    unvisitedInFragment.or(newEdges);
                    unvisitedInFragment.and(unvisited);
                }
            }

            //
            // Step 2.5: Derive all loop fragments workflow graphs
            //
            for (BitSet fragment: fragments) {
                BitSet fragLoopOut = (BitSet) loopOutgoing.clone();
                fragLoopOut.and(fragment);
                /*System.out.println("Fragment ");
                System.out.println(fragment);
                System.out.println(fragLoopOut);*/
                BitSet withoutLoopOut = (BitSet) fragment.clone();
                withoutLoopOut.andNot(fragLoopOut);
                WorkflowGraph fragmentWFG = createIterationBody(withoutLoopOut, cutoffEdges, fragLoopOut, true);

                SoundnessLoopDecompositionAnalysis loopDecomposition = new SoundnessLoopDecompositionAnalysis(fragmentWFG,
                        this.lastMapIterationBody,
                        reporter,
                        this.graph,
                        this.recursionDepth + 1);
                errors.addAll(loopDecomposition.compute());
                edgesVisited += loopDecomposition.getEdgesVisited();
                workflowGraphs.addAll(loopDecomposition.getDecomposition());
            }
            this.loopInformation.add(new LoopInformation(extComponent, doBody, cutoffEdges, loopIncoming,
                    loopOutgoing));
        }

        //
        // Step 3: Reduce the workflow graph
        //
        graph = reduce(graph);

        //
        // Step 4: Perform again a loop decomposition on the reduced workflow graph
        //
        SoundnessLoopDecompositionAnalysis loopDecomposition = new SoundnessLoopDecompositionAnalysis(graph,
                this.lastMap,
                reporter,
                this.graph,
                this.recursionDepth + 1);
        errors.addAll(loopDecomposition.compute());
        edgesVisited += loopDecomposition.getEdgesVisited();
        workflowGraphs.addAll(loopDecomposition.getDecomposition());

        // Report the number of edges
        reporter.put(this.origin, "NUMBER_VISITED_EDGES_DECOMPOSITION_" + recursionDepth, edgesVisited);
        reporter.put(this.origin, "NUMBER_LOOPS_" + recursionDepth, components.size());
        reporter.put(this.origin, "REDUCED_GRAPH_SIZE_EDGES_" + recursionDepth, graph.getEdges().size());
        reporter.put(this.origin, "REDUCED_GRAPH_SIZE_NODES_" + recursionDepth, graph.getNodeListInclusive().size());

        return errors;
    }

    /**
     * Apply rule 2, each loop entry is not an AND join.
     * @param component The loop.
     * @param loopIncoming The loop incoming edges.
     */
    private void applyRule2(BitSet component, BitSet loopIncoming) {
        for (int e = loopIncoming.nextSetBit(0); e >= 0; e = loopIncoming.nextSetBit(e + 1)) {
            edgesVisited++;
            Edge edge = edges.get(e);
            WGNode entry = edge.tgt;
            if (entry.getType() == WGNode.Type.JOIN) {
                DeadlockCycleAnnotation annotation = new DeadlockCycleAnnotation(this);
                annotation.addFailureNode(entry);
                annotation.addInvolvedNode(entry);
                annotation.addOpeningNode(entry);
                annotation.addPathToFailure(component);

                errors.add(annotation);
                reporter.add(graph, AnalysisInformation.NUMBER_DEADLOCKS_LOOP, 1);
            }
        }
    }

    /**
     * Apply rule 1, each loop exit is an XOR split.
     * @param component The loop.
     * @param loopOutgoing The loop outgoing edges.
     */
    private void applyRule1(BitSet component, BitSet loopOutgoing) {
        for (int o = loopOutgoing.nextSetBit(0); o >= 0; o = loopOutgoing.nextSetBit(o + 1)) {
            edgesVisited++;
            Edge edge = edges.get(o);
            WGNode exit = edge.src;
            if (exit.getType() != WGNode.Type.SPLIT) {
                AbundanceCycleAnnotation annotation = new AbundanceCycleAnnotation(this);
                annotation.addInvolvedNode(exit);
                annotation.addOpeningNode(exit);
                annotation.addPathToFailure(component);

                errors.add(annotation);
                reporter.add(graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_LOOP, 1);
            }
        }
    }
}
