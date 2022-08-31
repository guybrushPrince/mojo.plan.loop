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
package de.jena.uni.mojo.plan.plugin.loop.decomposition;

import de.jena.uni.mojo.analysis.Analysis;
import de.jena.uni.mojo.analysis.edge.Edge;
import de.jena.uni.mojo.analysis.edge.EdgeAnalysis;
import de.jena.uni.mojo.analysis.edge.StrongComponentsAnalysis;
import de.jena.uni.mojo.analysis.information.AnalysisInformation;
import de.jena.uni.mojo.error.Annotation;
import de.jena.uni.mojo.error.DeadlockCycleAnnotation;
import de.jena.uni.mojo.model.WGNode;
import de.jena.uni.mojo.model.WorkflowGraph;

import java.util.*;

/**
 * Class LoopDecomposition.
 * Extends a mojo analysis and performs a loop decomposition on a workflow graph described in the paper
 * ""
 * @author Dr. Dipl.-Inf. Thomas M. Prinz
 */
public class LoopDecomposition extends Analysis {

    /**
     * A serial version UID.
     */
    private static final long serialVersionUID = 5751831129981124751L;

    /**
     * The sub workflow graphs of this graph extracted through the loop decomposition.
     */
    protected final ArrayList<WorkflowGraph> workflowGraphs = new ArrayList<>();

    /**
     * The origin workflow graph.
     */
    protected final WorkflowGraph origin;

    /**
     * The recursion depth.
     */
    protected int recursionDepth = 0;

    /**
     * The list of edges.
     */
    protected final List<Edge> edges;

    /**
     * An array of bit sets where each bit set contains incoming edges of the
     * node with the id of the position in the array.
     */
    protected BitSet[] incoming;

    /**
     * An array of bit sets where each bit set contains outgoing edges of the
     * node with the id of the position in the array.
     */
    protected BitSet[] outgoing;

    /**
     * A list of errors.
     */
    protected final List<Annotation> errors = new ArrayList<>();

    /**
     * A counter of edges to determine the performance.
     */
    protected int edgesVisited = 0;

    /**
     * Loop information.
     */
    protected final List<LoopInformation> loopInformation = new ArrayList<>();

    /**
     * The last created node map.
     */
    protected WGNode[] lastMap;

    /**
     * The last created node map for the iteration body.
     */
    protected WGNode[] lastMapIterationBody;

    /**
     * The current maximum id.
     */
    protected int maxId = 0;

    /**
     * A bit set with free ids.
     */
    protected BitSet freeIds;

    /**
     * Constructor. This should be used for the entry of the analysis.
     * @param graph The workflow graph.
     * @param map The node map.
     * @param reporter The reporter.
     */
    public LoopDecomposition(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter) {
        super(graph, map, reporter);
        this.edges = graph.getEdges();
        this.incoming = graph.getIncomingEdges();
        this.outgoing = graph.getOutgoingEdges();
        this.origin = graph;
    }

    /**
     * Constructor. This constructor is used for recursive calls.
     * @param graph The workflow graph.
     * @param map The node map.
     * @param reporter The reporter.
     * @param origin The origin workflow graph.
     * @param recursionDepth The recursion depth.
     */
    protected LoopDecomposition(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter, WorkflowGraph origin,
                             int recursionDepth) {
        super(graph, map, reporter);
        this.edges = graph.getEdges();
        this.incoming = graph.getIncomingEdges();
        this.outgoing = graph.getOutgoingEdges();
        if (origin == null) this.origin = graph;
        else this.origin = origin;
        this.recursionDepth = recursionDepth;
    }

    @Override
    protected List<Annotation> analyze() {
        // Determine the largest id to assign new ids.
        this.maxId = graph.getNodeSet().size();
        // Determine the used ids so that unset ids can be recycled.
        this.freeIds = (BitSet) graph.getNodeSet().clone();
        this.freeIds.set(graph.getStart().getId());
        this.freeIds.set(graph.getEnd().getId());

        //
        // Step 1: Perform a strong component analysis and determine the strong components.
        //
        StrongComponentsAnalysis strongComponentsAnalysis = new StrongComponentsAnalysis(graph, map, reporter);
        strongComponentsAnalysis.compute();
        ArrayList<BitSet> loops = strongComponentsAnalysis.getComponents();


        //
        // If no cycles were found at all, add this workflow graph and return an empty list of errors.
        //
        if (loops.size() == 0) {
            workflowGraphs.add(graph);
            return Collections.emptyList();
        }

        //
        // Cycles found
        //
        WorkflowGraph graph = this.graph;

        //
        // Step 2: Iterate over each loop (strongly connected component).
        //
        // Define sets that are recycled.
        BitSet exitOutgoing = new BitSet(edges.size());
        BitSet entryIncoming = new BitSet(edges.size());
        for (BitSet loop : loops) {
            exitOutgoing.clear();
            entryIncoming.clear();

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
                        // Determine the inner-loop incoming edges of the loop entry.
                        entryIncoming.or(in);
                        entryIncoming.andNot(fromOut);
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

            // Create loop fragment that includes loop incoming and outgoing edges.
            BitSet extendedLoop = (BitSet) loop.clone();
            extendedLoop.or(loopIncoming);
            extendedLoop.or(loopOutgoing);

            //
            // Step 2.2: Find cutoff edges with a modified depth-first search.
            //
            // Cutoff edges can only be inner-loop outgoing edges of loop exits.
            BitSet cutoffEdges = (BitSet) exitOutgoing.clone();
            cutoffEdges.andNot(loopOutgoing);
            // Reduce the number of cutoff edges to get a connected iteration body.
            cutoffEdges = findCutoffEdges(extendedLoop, loopIncoming, cutoffEdges, entryIncoming);
            // Sometimes, cutoff edges cannot be determined to get a good iteration body. In such a case, take an
            // arbitrary inner-loop outgoing edge of a loop exit as cutoff edges.
            if (cutoffEdges.isEmpty()) {
                cutoffEdges.or(exitOutgoing);
                cutoffEdges.andNot(loopOutgoing);
                int cut = cutoffEdges.nextSetBit(0);
                cutoffEdges.clear();
                cutoffEdges.set(cut);
            }

            //
            // Step 2.3: Determine the do-body with a data-flow analysis.
            //
            // Set the generation/kill set for each incoming edge.
            HashMap<Integer, BitSet> gen = new HashMap<>();
            HashMap<Integer, BitSet> kill = new HashMap<>();
            HashMap<Integer, BitSet> doBody = new HashMap<>();
            int maxInfo = loopIncoming.cardinality();
            ArrayList<Integer> workingList = new ArrayList<>();

            // Initialize each edge of the component with an empty information set.
            for (int i = extendedLoop.nextSetBit(0); i >= 0; i = extendedLoop.nextSetBit(i + 1)) {
                // An edge is visited
                edgesVisited++;

                doBody.put(i, new BitSet(maxInfo));
                gen.put(i, new BitSet(maxInfo));
                kill.put(i, new BitSet(maxInfo));

                if (loopIncoming.get(i)) {
                    gen.get(i).set(i);
                    workingList.add(i);
                }
                if (cutoffEdges.get(i)) {
                    kill.get(i).flip(0, cutoffEdges.size());
                }
            }

            // Simple forward data-flow analysis
            BitSet in = new BitSet(maxInfo);
            BitSet subset = new BitSet(maxInfo);
            while (!workingList.isEmpty()) {
                // An edge is visited
                edgesVisited++;

                in.clear();
                subset.clear();

                // Get the first edge of the list
                int current = workingList.remove(0);

                // Get the outgoing edges
                BitSet incoming = (BitSet) this.incoming[edges.get(current).src.getId()].clone();
                incoming.and(extendedLoop);

                // Build IN information
                for (int j = incoming.nextSetBit(0); j >= 0; j = incoming.nextSetBit(j + 1)) {
                    // An edge is visited
                    edgesVisited++;
                    in.or(doBody.get(j));
                }
                // Remove KILL information
                in.andNot(kill.get(current));
                // Add GEN information
                in.or(gen.get(current));

                subset.or(in);
                subset.andNot(doBody.get(current));
                if (!subset.isEmpty()) {
                    // Some information has changed
                    doBody.put(current, (BitSet) in.clone());
                    // Add outgoing edges
                    // Get the outgoing edges
                    BitSet outgoing = (BitSet) this.outgoing[edges.get(current).tgt.getId()].clone();
                    outgoing.and(extendedLoop);
                    for (int j = outgoing.nextSetBit(0); j >= 0; j = outgoing.nextSetBit(j + 1)) {
                        // An edge is visited
                        edgesVisited++;

                        workingList.add(j);
                    }
                }
            }
            // Determine the do-body
            // Take a look at the edges and determine the do-body
            BitSet doBodyComponent = new BitSet(edges.size());
            for (int i = loop.nextSetBit(0); i >= 0; i = loop.nextSetBit(i + 1)) {
                // An edge is visited
                edgesVisited++;

                BitSet inf = doBody.get(i);
                if (!inf.isEmpty()) {
                    // The edge is part of the do-body
                    doBodyComponent.set(i);
                }
            }

            //
            // Step 2.4: Derive the loop workflow graph (iteration body)
            //
            WorkflowGraph iterationBody = createIterationBody(loop, cutoffEdges, loopOutgoing);
            LoopDecomposition loopDecomposition = new LoopDecomposition(iterationBody,
                    this.lastMapIterationBody,
                    reporter,
                    this.graph,
                    this.recursionDepth + 1);
            errors.addAll(loopDecomposition.compute());
            edgesVisited += loopDecomposition.getEdgesVisited();
            workflowGraphs.addAll(loopDecomposition.getDecomposition());

            // Store the information to reduce the workflow graph later
            this.loopInformation.add(new LoopInformation(loop, doBodyComponent, cutoffEdges, loopIncoming,
                    loopOutgoing));
        }

        //
        // Step 3: Reduce the workflow graph
        //
        graph = reduce(graph);

        //
        // Step 4: Perform again a loop decomposition on the reduced workflow graph
        //
        LoopDecomposition loopDecomposition = new LoopDecomposition(graph,
                this.lastMap,
                reporter,
                this.graph,
                this.recursionDepth + 1);
        errors.addAll(loopDecomposition.compute());
        edgesVisited += loopDecomposition.getEdgesVisited();
        workflowGraphs.addAll(loopDecomposition.getDecomposition());

        // Report the number of edges
        reporter.put(this.origin, "NUMBER_VISITED_EDGES_DECOMPOSITION_" + recursionDepth, edgesVisited);
        reporter.put(this.origin, "NUMBER_LOOPS_" + recursionDepth, loops.size());
        reporter.put(this.origin, "REDUCED_GRAPH_SIZE_EDGES_" + recursionDepth, graph.getEdges().size());
        reporter.put(this.origin, "REDUCED_GRAPH_SIZE_NODES_" + recursionDepth, graph.getNodeListInclusive().size());

        return errors;
    }

    /**
     * Get the result of the decomposition.
     * @return
     */
    public List<WorkflowGraph> getDecomposition() {
        return workflowGraphs;
    }

    /**
     * Find the cutoff edges.
     * @param extComponent The SCC with loop incoming and outgoing edges.
     * @param loopIncoming The loop incoming edges.
     * @param innerOutgoing The outgoing edges of loop exits within the loop.
     * @param innerIncoming The incoming edges of loop entries within the loop.
     * @return
     */
    private BitSet findCutoffEdges(BitSet extComponent, BitSet loopIncoming,
                                   BitSet innerOutgoing, BitSet innerIncoming) {
        BitSet cutoff = (BitSet) innerOutgoing.clone();

        // Determine a set representing the loop exits.
        BitSet cutoffNodes = new BitSet(map.length);
        for (int i = cutoff.nextSetBit(0); i >= 0; i = cutoff.nextSetBit(i + 1)) {
            edgesVisited++;
            cutoffNodes.set(edges.get(i).src.getId());
        }
        // Determine a set representing the loop entries.
        BitSet entryNodes = new BitSet(map.length);
        for (int i = innerIncoming.nextSetBit(0); i >= 0; i = innerIncoming.nextSetBit(i + 1)) {
            edgesVisited++;
            entryNodes.set(edges.get(i).tgt.getId());
        }

        // The DPE starts at the loop incoming edge.
        BitSet current = new BitSet(extComponent.size());
        current.or(loopIncoming);

        BitSet reached = new BitSet(map.length);
        BitSet tmp = new BitSet(map.length);
        BitSet inReached = new BitSet(extComponent.size());
        BitSet tmpEdges = new BitSet(extComponent.size());
        BitSet visited = new BitSet(extComponent.size());
        BitSet next = new BitSet(extComponent.size());

        // An iterative DPE
        boolean stable;
        do {
            while (!current.isEmpty()) {
                int c = current.nextSetBit(0);
                current.clear(c);
                visited.set(c);

                Edge edge = edges.get(c);
                next.clear();
                next.or(this.outgoing[edge.tgt.getId()]);
                next.and(extComponent);
                next.andNot(cutoff);
                next.andNot(visited);

                if (cutoffNodes.get(edge.tgt.getId()))
                    reached.set(edge.tgt.getId());
                if (entryNodes.get(edge.tgt.getId())) {
                    inReached.or(incoming[edge.tgt.getId()]);
                    inReached.and(innerIncoming);
                }

                current.or(next);
            }
            tmp.clear();
            tmp.or(cutoffNodes);
            tmp.and(reached);
            if (tmp.cardinality() < cutoffNodes.cardinality()) {
                // Not each loop exit reached.
                tmpEdges.clear();
                for (int i = reached.nextSetBit(0); i >= 0; i = reached.nextSetBit(i + 1)) {
                    tmpEdges.or(outgoing[i]);
                }
                tmpEdges.andNot(visited);
                current.set(tmpEdges.nextSetBit(0));
                stable = false;
            } else {
                tmp.clear();
                for (int i = entryNodes.nextSetBit(0); i >= 0; i = entryNodes.nextSetBit(i + 1)) {
                    edgesVisited++;
                    tmpEdges.clear();
                    tmpEdges.or(incoming[i]);
                    tmpEdges.and(innerIncoming);
                    tmpEdges.and(inReached);
                    if (tmpEdges.isEmpty()) tmp.set(i);
                }

                if (tmp.cardinality() >= 2) {
                    tmpEdges.clear();
                    for (int i = reached.nextSetBit(0); i >= 0; i = reached.nextSetBit(i + 1)) {
                        tmpEdges.or(outgoing[i]);
                    }
                    tmpEdges.andNot(visited);
                    current.set(tmpEdges.nextSetBit(0));
                    stable = false;
                } else {
                    stable = true;
                }
            }
        } while (!stable);

        cutoff.andNot(visited);

        return cutoff;
    }

    /**
     * Reduces the workflow graph by replacing its loops.
     * @param graph The workflow graph.
     * @return The reduced workflow graph.
     */
    protected WorkflowGraph reduce(WorkflowGraph graph) {
        // Create a new workflow graph for the reduced workflow.
        WorkflowGraph reduced = new WorkflowGraph();
        // Create a map for its nodes.
        HashMap<Integer, WGNode> nodes = new HashMap<>(this.map.length);

        // Collect all edges that should be removed from the original workflow graph.
        BitSet eliminate = null;
        for (LoopInformation loopInformation: this.loopInformation) {
            this.edgesVisited++;
            // Initialize the set.
            if (eliminate == null) eliminate = (BitSet) loopInformation.component.clone();
            // Add the loop.
            else eliminate.or(loopInformation.component);
            // And remove those edges from the do body.
            eliminate.andNot(loopInformation.doBody);
        }

        // Copy the workflow graph without the edges (and corresponding nodes) to eliminate.
        for (Edge edge : graph.getEdges()) {
            this.edgesVisited++;
            if (!eliminate.get(edge.id)) {
                WGNode src = this.getOrCreate(edge.src, reduced, nodes);
                WGNode tgt = this.getOrCreate(edge.tgt, reduced, nodes);
                src.addSuccessor(tgt);
                tgt.addPredecessor(src);
            }
        }

        // For each loop ...
        for (LoopInformation loopInformation: this.loopInformation) {
            this.edgesVisited++;
            // ... (1) Add loop node (combination of merge and split in this case)
            WGNode merge = new WGNode(this.getNextFreeId(), (loopInformation.loopIn.cardinality() == 1 ? WGNode.Type.ACTIVITY : WGNode.Type.MERGE));
            WGNode split = new WGNode(this.getNextFreeId(), (loopInformation.loopOut.cardinality() == 1 ? WGNode.Type.ACTIVITY : WGNode.Type.SPLIT));

            // The merge is before the split.
            merge.addSuccessor(split);
            split.addPredecessor(merge);

            // ... (2) Add edges TO the loop node (i.e., to the merge).
            // We need an edge to the merge only for cutoff edges.
            for (int c = loopInformation.cutoff.nextSetBit(0); c >= 0; c = loopInformation.cutoff.nextSetBit(c + 1)) {
                this.edgesVisited++;
                // Get the corresponding loop exit node.
                WGNode exit = edges.get(c).src;
                // Determine those incoming edges of the loop exit that actually are within the do-body.
                BitSet used = (BitSet) this.incoming[exit.getId()].clone();
                used.and(loopInformation.doBody);

                // The exit is actually used (reached) in the do-body.
                if (!used.isEmpty()) {
                    // Get or create the node that represents the loop exit.
                    WGNode src = this.getOrCreate(exit, reduced, nodes);
                    // If the merge contains already this exit as predecessor, then there are multiple edges
                    // coming from this loop exit to the loop node.
                    // We introduce a task (an activity in mojo slang) in this case between the loop exit and the loop
                    // node (merge).
                    if (merge.getPredecessorsBitSet().get(src.getId())) {
                        // Create the task ...
                        WGNode activity = new WGNode(this.getNextFreeId(), WGNode.Type.ACTIVITY);
                        nodes.put(activity.getId(), activity);
                        reduced.addNode(activity);
                        // ... add it as successor of the loop exit ...
                        src.addSuccessor(activity);
                        activity.addPredecessor(src);
                        // And set the task to the loop exit.
                        src = activity;
                    }
                    // Add the merge as successor.
                    src.addSuccessor(merge);
                    merge.addPredecessor(src);
                }
            }

            // ... (3) Add edges FROM the loop node (i.e., from the split).
            // We need an edge from the split only for loop outgoing edges.
            for (int o = loopInformation.loopOut.nextSetBit(0); o >= 0; o = loopInformation.loopOut.nextSetBit(o + 1)) {
                this.edgesVisited++;
                // TODO: New
                // Get the source (the loop exit) and the target of the loop outgoing edge.
                WGNode src = this.getOrCreate(edges.get(o).src, reduced, nodes);
                WGNode tgt = this.getOrCreate(edges.get(o).tgt, reduced, nodes);

                // Determine if some incoming edge of the target is within the do-body.
                BitSet used = (BitSet) this.incoming[tgt.getId()].clone();
                used.and(loopInformation.doBody);

                if (used.isEmpty() || tgt.getType() == WGNode.Type.MERGE) {
                    // The target is *not* reached by the do-body (therefore unconnected) ...
                    // ... or it is already a merge.
                    split.addSuccessor(tgt);
                    tgt.addPredecessor(split);
                } else {
                    // We have to introduce a new merge in front of the target
                    WGNode helpMerge = new WGNode(this.getNextFreeId(), WGNode.Type.MERGE);
                    nodes.put(helpMerge.getId(), helpMerge);
                    reduced.addNode(helpMerge);

                    if (!used.isEmpty()) {
                        // Remove old information.
                        src.removeSuccessor(tgt);
                        tgt.removePredecessor(src);

                        // Add the help merge as successor of the loop exit (src).
                        src.addSuccessor(helpMerge);
                        helpMerge.addPredecessor(src);
                    }

                    // Add the help merge as successor of the split node
                    split.addSuccessor(helpMerge);
                    helpMerge.addPredecessor(split);

                    // Set the target as successor of the help merge.
                    helpMerge.addSuccessor(tgt);
                    tgt.addPredecessor(helpMerge);
                }

                /*
                // THIS PART IS STRANGE.

                // Determine if this loop outgoing edge is within the do-body.
                BitSet used = (BitSet) this.incoming[exit.getId()].clone();
                used.and(loopInformation.doBody);


                if (used.get(o)) {
                    WGNode src = this.getOrCreate(edges.get(o).src, reduced, nodes);
                    WGNode tgt = this.getOrCreate(edges.get(o).tgt, reduced, nodes);
                    if (tgt.getType() != WGNode.Type.MERGE) {
                        // We have to introduce a new merge
                        WGNode helpMerge = new WGNode(this.getNextFreeId(), WGNode.Type.MERGE);
                        nodes.put(helpMerge.getId(), helpMerge);

                        reduced.addNode(helpMerge);
                        src.removeSuccessor(tgt);
                        tgt.removePredecessor(src);

                        src.addSuccessor(helpMerge);
                        helpMerge.addPredecessor(src);

                        split.addSuccessor(helpMerge);
                        helpMerge.addPredecessor(split);

                        helpMerge.addSuccessor(tgt);
                        tgt.addPredecessor(helpMerge);
                    } else {
                        split.addSuccessor(tgt);
                        tgt.addPredecessor(split);
                    }
                } else {
                    WGNode tgt = getOrCreate(edges.get(o).tgt, reduced, nodes);
                    split.addSuccessor(tgt);
                    tgt.addPredecessor(split);
                }*/
            }

            // Set the final type of merge
            merge.setType(merge.getPredecessors().size() == 1 ? WGNode.Type.ACTIVITY : WGNode.Type.MERGE);
            nodes.put(merge.getId(), merge);
            reduced.addNode(merge);
            // Set the final type of split
            split.setType(split.getSuccessors().size() == 1 ? WGNode.Type.ACTIVITY : WGNode.Type.SPLIT);
            nodes.put(split.getId(), split);
            reduced.addNode(split);

            // Correct the nodes previously being merges or splits
            this.correctNodes(reduced, nodes.values(), loopInformation.component);
        }

        // Finalize the workflow graph.
        this.lastMap = this.createNodeMap(nodes.values());
        // Perform an edge analysis.
        EdgeAnalysis edgeAnalysis = new EdgeAnalysis(reduced, lastMap, reporter);
        edgeAnalysis.compute();

        return reduced;
    }

    /**
     * Get the next free id.
     * @return Next free id.
     */
    private int getNextFreeId() {
        int free = this.freeIds.nextClearBit(0);
        if (free >= 0) {
            this.freeIds.set(free);
            return free;
        } else {
            return this.maxId++;
        }
    }

    /**
     * Creates the iteration body out of the loop.
     * @param component The component (the original loop).
     * @param cutoff The set of cutoff edges.
     * @param loopOut The set of edges going out of the loop.
     * @return The iteration body workflow graph.
     */
    protected WorkflowGraph createIterationBody(BitSet component, BitSet cutoff, BitSet loopOut) {
        return this.createIterationBody(component, cutoff,  loopOut, false);
    }

    /**
     * Creates the iteration body out of the loop.
     * @param component The component (the original loop).
     * @param cutoff The set of cutoff edges.
     * @param loopOut The set of edges going out of the loop.
     * @param isFragment Whether the iteration body is a fragment.
     * @return The iteration body workflow graph.
     */
    protected WorkflowGraph createIterationBody(BitSet component, BitSet cutoff, BitSet loopOut, boolean isFragment) {
        // Create a new workflow graph for the iteration body (fragment).
        WorkflowGraph graph = new WorkflowGraph();
        HashMap<Integer, WGNode> nodes = new HashMap<>(this.map.length);
        // Store the maximum id locally since the ids can be recycled.
        int maxId = this.maxId;

        // Create a new start node
        WGNode start = new WGNode(maxId++, WGNode.Type.START);
        nodes.put(start.getId(), start);
        graph.setStart(start);

        // If there are more than 1 cutoff edges, the fragment has more than one start node.
        // Remember: All start nodes are exclusive.
        if (cutoff.cardinality() >= 2) {
            // Create a split in this case ...
            WGNode split = new WGNode(maxId++, WGNode.Type.SPLIT);
            nodes.put(split.getId(), split);
            graph.addNode(split);

            // ... connect it to the start ...
            start.addSuccessor(split);
            split.addPredecessor(start);

            // ... and use it as a start.
            start = split;
        }

        // Create a new end node
        WGNode end = new WGNode(maxId++, WGNode.Type.END);
        nodes.put(end.getId(), end);
        graph.setEnd(end);

        // If there is more than 1 cutoff edge or loop-outgoing edge, the fragment has more than one end node.
        // Remember: All end nodes are exclusive.
        if (cutoff.cardinality() + loopOut.cardinality() >= 2) {
            // Create a merge in this case ...
            WGNode merge = new WGNode(maxId++, WGNode.Type.MERGE);
            nodes.put(merge.getId(), merge);
            graph.addNode(merge);

            // ... connect it with the end ...
            merge.addSuccessor(end);
            end.addPredecessor(merge);

            // ... and use it as end.
            end = merge;
        }

        // A set to store targets of cutoff edges within the loop.
        BitSet fromCut = new BitSet(component.size());
        // A set to store sources of cutoff and loop outgoing edges of loops.
        BitSet toCutOut = new BitSet(component.size());

        // Copy each element of the component
        for (int i = component.nextSetBit(0); i >= 0; i = component.nextSetBit(i + 1)) {
            this.edgesVisited++;

            // Get the edge.
            Edge edge = edges.get(i);
            // If it is a cutoff edge ...
            if (cutoff.get(i)) {
                // ... and it is not a fragment ...
                if (!isFragment) {
                    // The source and target.
                    WGNode newSrc = this.getOrCreate(edges.get(i).src, graph, nodes);
                    WGNode newTgt = this.getOrCreate(edges.get(i).tgt, graph, nodes);

                    // ... connect it to the start and end.
                    start.addSuccessor(newTgt);
                    newTgt.addPredecessor(start);
                    end.addPredecessor(newSrc);
                    newSrc.addSuccessor(end);
                }
            } else {
                // ... else copy it.
                // Copy the src and target.
                WGNode src = edge.src;
                WGNode tgt = edge.tgt;
                WGNode newSrc = this.getOrCreate(src, graph, nodes);
                WGNode newTgt = this.getOrCreate(tgt, graph, nodes);

                // Connect them.
                newSrc.addSuccessor(newTgt);
                newTgt.addPredecessor(newSrc);

                // Check if the source of the edge is the target of a cutoff edge.
                BitSet in = this.incoming[newSrc.getId()];
                in = (BitSet) in.clone();
                in.and(cutoff);
                fromCut.or(in);

                // Check if the target of the edge is the source of a cutoff or loop outgoing edge.
                BitSet out = this.outgoing[newTgt.getId()];
                BitSet cutClone = (BitSet) cutoff.clone();
                cutClone.or(loopOut);
                cutClone.and(out);
                toCutOut.or(cutClone);
            }
        }
        // If it is a fragment.
        if (isFragment) {
            ArrayList<WGNode> newNodes = new ArrayList<>();
            // For each edge being the target of a cutoff edge in the fragment.
            for (int i = fromCut.nextSetBit(0); i >= 0; i = fromCut.nextSetBit(i + 1)) {
                this.edgesVisited++;
                // Create the target node.
                WGNode newTgt = getOrCreate(edges.get(i).tgt, graph, nodes);

                // Connect it with the start node ...
                if (start.getSuccessorsBitSet().get(newTgt.getId())) {
                    // ... and introduce a new task / activity between them if necessary.
                    WGNode activity = new WGNode(maxId++, WGNode.Type.ACTIVITY);
                    newNodes.add(activity);
                    graph.addNode(activity);
                    newTgt.addPredecessor(activity);
                    activity.addSuccessor(newTgt);
                    newTgt = activity;
                }
                start.addSuccessor(newTgt);
                newTgt.addPredecessor(start);
            }
            // For each edge being the source of a cutoff edge or loop outgoing edge in the fragment.
            for (int i = toCutOut.nextSetBit(0); i >= 0; i = toCutOut.nextSetBit(i + 1)) {
                this.edgesVisited++;
                // Create the source node.
                WGNode newSrc = getOrCreate(edges.get(i).src, graph, nodes);

                // Connect it with the end node ...
                if (end.getPredecessorsBitSet().get(newSrc.getId())) {
                    // ... and introduce a new task / activity between them if necessary.
                    WGNode activity = new WGNode(maxId++, WGNode.Type.ACTIVITY);
                    newNodes.add(activity);
                    graph.addNode(activity);
                    activity.addPredecessor(newSrc);
                    newSrc.addSuccessor(activity);
                    newSrc = activity;
                }
                end.addPredecessor(newSrc);
                newSrc.addSuccessor(end);
            }
            // Add the newly created nodes to the node list.
            for (WGNode node: newNodes) {
                nodes.put(node.getId(), node);
            }
        }

        // Correct nodes that are broken.
        this.correctNodes(graph, nodes.values(), component);

        // Finalize the workflow graph.
        this.lastMapIterationBody = this.createNodeMap(nodes.values());
        EdgeAnalysis edgeAnalysis = new EdgeAnalysis(graph, this.lastMapIterationBody, reporter);
        edgeAnalysis.compute();

        return graph;
    }

    /**
     * Creates the node map.
     * @param nodes The nodes.
     * @return A node map.
     */
    private WGNode[] createNodeMap(Collection<WGNode> nodes) {
        // Create a node map.
        int length = 0;
        for (WGNode node: nodes) {
            edgesVisited++;
            length = Math.max(node.getId(), length) + 1;
        }
        WGNode[] map = new WGNode[length];
        for (WGNode node : nodes) {
            edgesVisited++;
            if (node != null) {
                map[node.getId()] = node;
            }
        }
        return map;
    }

    /**
     * Get or creates a node for an old one.
     * @param old The old node.
     * @param graph The workflow graph to add the node.
     * @param nodes The map of nodes.
     * @return A got or created workflow node.
     */
    private WGNode getOrCreate(WGNode old, WorkflowGraph graph, HashMap<Integer, WGNode> nodes) {
        if (nodes.get(old.getId()) == null) {
            WGNode node = new WGNode(old.getId(), old.getType());
            node.addProcessElement(old);
            if (node.getType() != WGNode.Type.END && node.getType() != WGNode.Type.START) graph.addNode(node);
            else if (node.getType() == WGNode.Type.END) graph.setEnd(node);
            else graph.setStart(node);
            nodes.put(old.getId(), node);
            return node;
        } else return nodes.get(old.getId());
    }

    /**
     * Correct nodes by setting their type from join/merge/split/fork to activity if necessary.
     * In doing this, rule 4 from the paper - each broken join must be an XOR- or OR-join - is checked.
     * @param graph The workflow graph.
     * @param nodes The nodes.
     * @param component The component.
     */
    private void correctNodes(WorkflowGraph graph, Collection<WGNode> nodes, BitSet component) {
        // Correct nodes
        for (WGNode node: nodes) {
            this.edgesVisited++;
            if (node != null) {
                // An XOR, OR, or AND join becomes an activity.
                if (node.getType() == WGNode.Type.JOIN || node.getType() == WGNode.Type.MERGE ||
                        node.getType() == WGNode.Type.OR_JOIN) {
                    if (node.getPredecessors().size() == 1) {
                        if (node.getType() == WGNode.Type.JOIN) {
                            // It is a deadlock situation.
                            DeadlockCycleAnnotation annotation = new DeadlockCycleAnnotation(this);
                            annotation.addFailureNode(node);
                            annotation.addInvolvedNode(node);
                            annotation.addOpeningNode(node);
                            annotation.addPathToFailure(component);

                            errors.add(annotation);
                            reporter.add(graph, AnalysisInformation.NUMBER_DEADLOCKS_LOOP, 1);
                        }
                        // The node is removed and added as an activity (task).
                        graph.removeNode(node);
                        node.setType(WGNode.Type.ACTIVITY);
                        graph.addNode(node);
                    }
                } else if (node.getType() == WGNode.Type.SPLIT) {
                    if (node.getSuccessors().size() == 1) {
                        // The node is removed and added as an activity (task).
                        graph.removeNode(node);
                        node.setType(WGNode.Type.ACTIVITY);
                        graph.addNode(node);
                    }
                }
            }
        }
    }

    /**
     * Get the number of visited edges.
     * @return Number of visited edges.
     */
    protected int getEdgesVisited() {
        return this.edgesVisited;
    }

}
