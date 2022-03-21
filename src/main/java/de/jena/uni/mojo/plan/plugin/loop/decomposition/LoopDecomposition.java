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
 *
 */
public class LoopDecomposition  extends Analysis {

    /**
     * The sub workflow graphs of this graph.
     */
    private final ArrayList<WorkflowGraph> workflowGraphs = new ArrayList<>();

    /**
     * The origin workflow graph.
     */
    private final WorkflowGraph origin;

    /**
     * The recursion depth.
     */
    private int recursionDepth = 0;

    /**
     * The list of edges.
     */
    private final List<Edge> edges;

    /**
     * An array of bit sets where each bit set contains incoming edges of the
     * node with the id of the position in the array.
     */
    private BitSet[] incoming;

    /**
     * An array of bit sets where each bit set contains outgoing edges of the
     * node with the id of the position in the array.
     */
    private BitSet[] outgoing;

    /**
     * A list of errors.
     */
    private final List<Annotation> errors = new ArrayList<>();

    /**
     * A counter of edges to determine the performance.
     */
    private int edgesVisited = 0;

    /**
     * Loop information.
     */
    private final List<LoopInformation> loopInformation = new ArrayList<>();

    /**
     * The last created node map.
     */
    private WGNode[] lastMap;

    /**
     * The last created node map for the iteration body.
     */
    private WGNode[] lastMapIterationBody;

    /**
     * The current maximum id.
     */
    private int maxId = 0;

    /**
     * A bit set with free ids.
     */
    private BitSet freeIds;

    /**
     * Constructor.
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
        this.recursionDepth = 0;
    }

    /**
     * Constructor.
     * @param graph The workflow graph.
     * @param map The node map.
     * @param reporter The reporter.
     * @param origin The origin workflow graph.
     * @param recursionDepth The recursion depth.
     */
    private LoopDecomposition(WorkflowGraph graph, WGNode[] map, AnalysisInformation reporter, WorkflowGraph origin,
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
        this.freeIds = (BitSet) graph.getNodeSet().clone();
        this.freeIds.set(graph.getStart().getId());
        this.freeIds.set(graph.getEnd().getId());

        //
        // Step 1: Perform strong component analysis.
        //
        StrongComponentsAnalysis strongComponentsAnalysis = new StrongComponentsAnalysis(graph, map, reporter);
        strongComponentsAnalysis.compute();
        ArrayList<BitSet> components = strongComponentsAnalysis.getComponents();

        // If no cycles where found at all, return only the workflow graph.
        if (components.size() == 0) {
            workflowGraphs.add(graph);
            return Collections.emptyList();
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

            // Create a SCC that includes loop incoming and outgoing edges.
            BitSet extComponent = (BitSet) component.clone();
            extComponent.or(loopIncoming);
            extComponent.or(loopOutgoing);

            //
            // Step 2.2: Find cutoff edges with a modified depth-first search.
            //
            BitSet cutoffEdges = (BitSet) exitOutgoing.clone();
            cutoffEdges.andNot(loopOutgoing);
            cutoffEdges = findCutoffEdges(extComponent, loopIncoming, cutoffEdges, entryIncoming);
            // Fallback
            if (cutoffEdges.isEmpty()) {
                cutoffEdges.or(exitOutgoing);
                cutoffEdges.andNot(loopOutgoing);
                int cut = cutoffEdges.nextSetBit(0);
                cutoffEdges.clear();
                cutoffEdges.set(cut);
            }

            //
            // Step 2.3: Determine the do-body with a data-flow analysis
            //
            // Set the generation/kill set for each incoming edge.
            HashMap<Integer, BitSet> gen = new HashMap<>();
            HashMap<Integer, BitSet> kill = new HashMap<>();
            HashMap<Integer, BitSet> doBody = new HashMap<>();
            int maxInfo = loopIncoming.cardinality();
            ArrayList<Integer> workingList = new ArrayList<>();

            // Initialize each edge of the component with an empty information set.
            for (int i = extComponent.nextSetBit(0); i >= 0; i = extComponent.nextSetBit(i + 1)) {
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
                incoming.and(extComponent);

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
                    outgoing.and(extComponent);
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
            for (int i = component.nextSetBit(0); i >= 0; i = component.nextSetBit(i + 1)) {
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
            WorkflowGraph iterationBody = createIterationBody(component, cutoffEdges, loopOutgoing);
            LoopDecomposition loopDecomposition = new LoopDecomposition(iterationBody,
                    this.lastMapIterationBody,
                    reporter,
                    this.graph,
                    this.recursionDepth + 1);
            errors.addAll(loopDecomposition.compute());
            workflowGraphs.addAll(loopDecomposition.getDecomposition());

            // Store the information to reduce the workflow graph later
            this.loopInformation.add(new LoopInformation(component, doBodyComponent, cutoffEdges, loopIncoming,
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
        workflowGraphs.addAll(loopDecomposition.getDecomposition());

        // Report the number of edges
        reporter.put(this.origin, "NUMBER_VISITED_EDGES_DECOMPOSITION_" + recursionDepth, edgesVisited);
        reporter.put(this.origin, "NUMBER_LOOPS_" + recursionDepth, components.size());
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
     * Reduces the workflow graph by loops.
     * @param graph The workflow graph.
     * @return The reduced workflow graph.
     */
    private WorkflowGraph reduce(WorkflowGraph graph) {
        // Create a new workflow graph for the reduced workflow.
        WorkflowGraph reduced = new WorkflowGraph();
        HashMap<Integer, WGNode> nodes = new HashMap<>(this.map.length);

        BitSet eliminate = null;
        for (LoopInformation loopInformation: this.loopInformation) {
            if (eliminate == null) eliminate = (BitSet) loopInformation.component.clone();
            else eliminate.or(loopInformation.component);
            eliminate.andNot(loopInformation.doBody);
        }

        // Copy the workflow graph without the edges (and corresponding nodes) to eliminate.
        for (Edge edge : graph.getEdges()) {
            edgesVisited++;
            if (!eliminate.get(edge.id)) {
                WGNode src = getOrCreate(edge.src, reduced, nodes);
                WGNode tgt = getOrCreate(edge.tgt, reduced, nodes);
                src.addSuccessor(tgt);
                tgt.addPredecessor(src);
            }
        }

        for (LoopInformation loopInformation: this.loopInformation) {
            // Add loop node (combination of merge and split in this case)
            WGNode merge = new WGNode(this.getNextFreeId(), (loopInformation.loopIn.cardinality() == 1 ? WGNode.Type.ACTIVITY : WGNode.Type.MERGE));
            nodes.put(merge.getId(), merge);
            reduced.addNode(merge);

            WGNode split = new WGNode(this.getNextFreeId(), (loopInformation.loopOut.cardinality() == 1 ? WGNode.Type.ACTIVITY : WGNode.Type.SPLIT));
            nodes.put(split.getId(), split);
            reduced.addNode(split);

            merge.addSuccessor(split);
            split.addPredecessor(merge);

            // Add edges TO the loop node
            for (int i = loopInformation.cutoff.nextSetBit(0); i >= 0; i = loopInformation.cutoff.nextSetBit(i + 1)) {
                edgesVisited++;
                WGNode src = getOrCreate(edges.get(i).src, reduced, nodes);
                src.addSuccessor(merge);
                merge.addPredecessor(src);
            }

            // Add edges FROM the loop node
            for (int i = loopInformation.loopOut.nextSetBit(0); i >= 0; i = loopInformation.loopOut.nextSetBit(i + 1)) {
                edgesVisited++;
                if (!eliminate.get(i)) {
                    WGNode src = getOrCreate(edges.get(i).src, reduced, nodes);
                    WGNode tgt = getOrCreate(edges.get(i).tgt, reduced, nodes);
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
                        src.addSuccessor(tgt);
                        tgt.addPredecessor(src);
                        split.addSuccessor(tgt);
                        tgt.addPredecessor(split);
                    }
                }
            }

            // Correct the nodes previously being merges or splits
            correctNodes(nodes.values(), loopInformation.component);
        }

        // Finalize the workflow graph.
        this.lastMap = createNodeMap(nodes.values());
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
    private WorkflowGraph createIterationBody(BitSet component, BitSet cutoff, BitSet loopOut) {
        WorkflowGraph graph = new WorkflowGraph();
        HashMap<Integer, WGNode> nodes = new HashMap<>(this.map.length);
        int maxId = this.maxId;

        // Create a new start node
        WGNode start = new WGNode(maxId++, WGNode.Type.START);
        nodes.put(start.getId(), start);
        graph.setStart(start);

        if (cutoff.cardinality() >= 2) {
            WGNode split = new WGNode(maxId++, WGNode.Type.SPLIT);
            nodes.put(split.getId(), split);
            graph.addNode(split);

            start.addSuccessor(split);
            split.addPredecessor(start);
            start = split;
        }

        // Create a new end node
        WGNode end = new WGNode(maxId++, WGNode.Type.END);
        nodes.put(end.getId(), end);
        graph.setEnd(end);

        if (cutoff.cardinality() + loopOut.cardinality() >= 2) {
            WGNode merge = new WGNode(maxId++, WGNode.Type.MERGE);
            nodes.put(merge.getId(), merge);
            graph.addNode(merge);

            merge.addSuccessor(end);
            end.addPredecessor(merge);

            end = merge;
        }

        // Copy each element of the component
        for (int i = component.nextSetBit(0); i >= 0; i = component.nextSetBit(i + 1)) {
            edgesVisited++;

            Edge edge = edges.get(i);
            if (cutoff.get(i)) {
                // The source and target.
                WGNode newSrc = getOrCreate(edges.get(i).src, graph, nodes);
                WGNode newTgt = getOrCreate(edges.get(i).tgt, graph, nodes);

                // Connect them
                start.addSuccessor(newTgt);
                newTgt.addPredecessor(start);
                end.addPredecessor(newSrc);
                newSrc.addSuccessor(end);
            } else {
                WGNode src = edge.src;
                WGNode tgt = edge.tgt;
                WGNode newSrc = getOrCreate(src, graph, nodes);
                WGNode newTgt = getOrCreate(tgt, graph, nodes);

                newSrc.addSuccessor(newTgt);
                newTgt.addPredecessor(newSrc);
            }
        }

        // Introduce a merge and end node for each outgoing edge.
        for (int i = loopOut.nextSetBit(0); i >= 0; i = loopOut.nextSetBit(i + 1)) {
            edgesVisited++;

            // Get the source.
            WGNode newSrc = getOrCreate(edges.get(i).src, graph, nodes);
            newSrc.addSuccessor(end);
            end.addPredecessor(newSrc);
        }

        correctNodes(nodes.values(), component);

        // Finalize the workflow graph.
        this.lastMapIterationBody = createNodeMap(nodes.values());
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
     * @param nodes The nodes.
     * @param component The component.
     */
    private void correctNodes(Collection<WGNode> nodes, BitSet component) {
        // Correct nodes
        for (WGNode node: nodes) {
            edgesVisited++;
            if (node != null) {
                if (node.getType() == WGNode.Type.JOIN || node.getType() == WGNode.Type.MERGE ||
                        node.getType() == WGNode.Type.OR_JOIN) {
                    if (node.getPredecessors().size() == 1) {
                        node.setType(WGNode.Type.ACTIVITY);

                        if (node.getType() == WGNode.Type.JOIN) {
                            DeadlockCycleAnnotation annotation = new DeadlockCycleAnnotation(this);
                            annotation.addFailureNode(node);
                            annotation.addInvolvedNode(node);
                            annotation.addOpeningNode(node);
                            annotation.addPathToFailure(component);

                            errors.add(annotation);
                            reporter.add(graph, AnalysisInformation.NUMBER_DEADLOCKS_LOOP, 1);
                            reporter.endIgnoreTimeMeasurement(graph, this.getClass().getName());
                        }
                    }
                }
            }
        }
    }

    private class LoopInformation {
        public final BitSet component;
        public final BitSet doBody;
        public final BitSet cutoff;
        public final BitSet loopIn;
        public final BitSet loopOut;

        private LoopInformation(BitSet component, BitSet doBody, BitSet cutoff, BitSet loopIn, BitSet loopOut) {
            this.component = component;
            this.doBody = doBody;
            this.cutoff = cutoff;
            this.loopIn = loopIn;
            this.loopOut = loopOut;
        }
    }
}
