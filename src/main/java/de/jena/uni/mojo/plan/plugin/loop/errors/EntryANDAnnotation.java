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
package de.jena.uni.mojo.plan.plugin.loop.errors;

import de.jena.uni.mojo.analysis.Analysis;
import de.jena.uni.mojo.analysis.edge.Edge;
import de.jena.uni.mojo.error.Annotation;
import de.jena.uni.mojo.error.EAlarmCategory;
import de.jena.uni.mojo.error.marker.Marker;
import de.jena.uni.mojo.interpreter.AbstractEdge;
import de.jena.uni.mojo.interpreter.IdInterpreter;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.List;

/**
 * Class EntryANDAnnotation.
 * A class representing a soundness violation that a loop entry is an AND.
 *
 * @author Dr. Dipl.-Inf. Thomas M. Prinz
 */
public class EntryANDAnnotation extends Annotation {

    /**
     * The failure description.
     */
    public static final String DESCRIPTION = "This loop has an entry that is a parallel gateway (AND).";

    /**
     * The name of the path to failure attribute.
     */
    public static final String PATH_TO_FAILURE = "PathToFailure";

    /**
     * Defines paths from the source of the failure to the wrong merging node.
     */
    private final List<BitSet> pathsToFailure = new ArrayList<BitSet>();

    /**
     * The constructor defines an abundance annotation and hides the information
     * about the description and the alarm category.
     *
     * @param analysis
     *            The analysis which defines this annotation.
     */
    public EntryANDAnnotation(Analysis analysis) {
        this(DESCRIPTION, analysis);
    }

    /**
     * The constructor defines an abundance annotation and hides the information
     * about the alarm category.
     *
     * @param description
     *            The description of the failure annotation.
     * @param analysis
     *            The analysis which defines this annotation.
     */
    protected EntryANDAnnotation(String description, Analysis analysis) {
        super(EAlarmCategory.ERROR, description, analysis);
    }

    /**
     * Get the paths to the failure.
     *
     * @return the pathToFailure
     */
    public List<BitSet> getPathsToFailure() {
        return pathsToFailure;
    }

    /**
     * Add the paths to the failure.
     *
     * @param pathsToFailure
     *            the paths to the failure to add
     */
    public void addPathsToFailure(Collection<BitSet> pathsToFailure) {
        this.pathsToFailure.addAll(pathsToFailure);
    }

    /**
     * Add a single path to the failure.
     *
     * @param pathToFailure
     *            the path to failure to add.
     */
    public void addPathToFailure(BitSet pathToFailure) {
        this.pathsToFailure.add(pathToFailure);
    }

    @Override
    public void printInformation(IdInterpreter interpreter) {
        super.printInformation(interpreter);

        System.out.printf("\t\t%-35s: %n", "Paths to the fault (WFG + Process)");

        int pathCounter = 0;
        for (BitSet path : this.pathsToFailure) {
            pathCounter++;

            // Extract the workflow graph edges
            List<Edge> wfgEdges = this.extractEdgePath(path);

            System.out.printf("\t\t\t%-20s: %s%n", "Path " + pathCounter + " (WFG)",
                    wfgEdges.toString());

            // Print the process nodes
            System.out.printf("\t\t\t%-20s: %s%n",
                    "Path " + pathCounter + " (Process)",
                    interpreter.extractPath(this.extractAbstractPath(wfgEdges)));
        }

    }

    @Override
    public Marker interpret(IdInterpreter interpreter) {
        Marker marker = super.interpret(interpreter);

        // Add additional information
        int pathCounter = 0;
        for (BitSet path : pathsToFailure) {
            // Extract the workflow graph edges
            List<Edge> wfgEdges = this.extractEdgePath(path);
            // Extract the origin objects
            List<AbstractEdge> processEdges = this.extractAbstractPath(wfgEdges);

            marker.addProcessAnnotation(PATH_TO_FAILURE,
                    interpreter.extractPath(processEdges), 4 + (pathCounter++));
        }

        return marker;
    }
}
