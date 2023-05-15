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
package de.jena.uni.mojo.plan.plugin.loop.plan;


import de.jena.uni.mojo.Mojo;
import de.jena.uni.mojo.analysis.edge.EdgeAnalysis;
import de.jena.uni.mojo.analysis.information.AnalysisInformation;
import de.jena.uni.mojo.annotations.MajorAnalysisPlan;
import de.jena.uni.mojo.error.*;
import de.jena.uni.mojo.general.MajorPlan;
import de.jena.uni.mojo.model.WGNode;
import de.jena.uni.mojo.model.WorkflowGraph;
import de.jena.uni.mojo.plan.PreparationPlan;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.LoopDecomposition;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.soundness.SoundnessLoopDecompositionAnalysis;
import de.jena.uni.mojo.plan.plugin.loop.errors.EntryANDAnnotation;
import de.jena.uni.mojo.plan.plugin.loop.errors.ExitNotXORAnnotation;
import de.jena.uni.mojo.plan.plugin.loop.errors.LivelockAnnotation;
import de.jena.uni.mojo.util.export.WorkflowGraphExporter;
import de.jena.uni.mojo.util.store.ElementStore;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * The Loop decomposition major plan performs a Loop decomposition with soundness analysis.
 * 
 * @author Dipl.-Inf. Thomas M. Prinz
 * 
 */
@MajorAnalysisPlan(id = 5, name = "Loop Decomposition Major Plan", author = "Dr. Dipl.-Inf. Thomas M. Prinz", description = "The Loop decomposition major plan performs a Loop decomposition with soundness analysis.")
public class SoundnessDecompositionMajorPlan extends MajorPlan {

	/**
	 * The serial version UID.
	 */
	private static final long serialVersionUID = -2453357124463678034L;

	/**
	 * The store in which all elements are stored.
	 */
	private final ElementStore store;

	/**
	 * The constructor.
	 *
	 * @param graph
	 *            The workflow graph.
	 * @param map
	 *            A node id to node map for a fast analysis.
	 * @param analysisInformation
	 *            An analysis information map.
	 * @param store
	 *            The element store.
	 */
	public SoundnessDecompositionMajorPlan(WorkflowGraph graph, WGNode[] map,
                                           AnalysisInformation analysisInformation, ElementStore store) {
		super(graph, map, analysisInformation);
		this.store = store;
	}

	@Override
	protected void execute() {

		//
		// 1. Prepare the workflow graph
		//
		PreparationPlan preparationPlan = new PreparationPlan(graph, map,
				analysisInformation, store);
		List<Annotation> preparationErrors = preparationPlan.compute();
		for (Annotation error: preparationErrors) {
			if (error.getAlarmCategory() == EAlarmCategory.ERROR) this.errorList.add(error);
		}
		//this.errorList.addAll(preparationErrors);
		this.map = preparationPlan.getMap();

		//
		// 2. Perform edge analysis
		//
		EdgeAnalysis edgeAnalysis = new EdgeAnalysis(graph, map, reporter);
		edgeAnalysis.compute();

		//
		// 3: Perform the loop decomposition with soundness
		//
		SoundnessLoopDecompositionAnalysis decomposition =
				new SoundnessLoopDecompositionAnalysis(graph, map, analysisInformation, store);
		List<Annotation> decompositionErrors = decomposition.compute().stream().distinct().collect(Collectors.toList());
		for (Annotation error: decompositionErrors) {
			if (error.getAlarmCategory() == EAlarmCategory.ERROR) this.errorList.add(error);
		}


		// Report information
		reporter.put(this.graph, "ERRORS_DECOMPOSITION", this.errorList.size());

		reporter.put(this.graph, "livelocks", 0);
		reporter.put(this.graph, "loop_entry_violations", 0);
		reporter.put(this.graph, "loop_exit_violations", 0);
		reporter.put(this.graph, "loop_without_entry", 0);
		reporter.put(this.graph, AnalysisInformation.NUMBER_DEADLOCKS, 0);
		reporter.put(this.graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION, 0);
		for (Annotation error: this.errorList) {
			if (error instanceof DeadlockAnnotation) {
				reporter.add(this.graph, AnalysisInformation.NUMBER_DEADLOCKS, 1);
				if (error instanceof DeadlockCycleAnnotation) {
					reporter.add(this.graph, AnalysisInformation.NUMBER_DEADLOCKS_LOOP, 1);
				} else {
					reporter.add(this.graph, AnalysisInformation.NUMBER_DEADLOCKS_NORMAL, 1);
				}
			} else if (error instanceof AbundanceAnnotation) {
				reporter.add(this.graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION, 1);
				if (error instanceof AbundanceCycleAnnotation) {
					reporter.add(this.graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_LOOP, 1);
				} else {
					reporter.add(this.graph, AnalysisInformation.NUMBER_LACK_OF_SYNCHRONIZATION_NORMAL, 1);
				}
			} else if (error instanceof LivelockAnnotation) {
				reporter.add(this.graph, "livelocks", 1);
			} else if (error instanceof EntryANDAnnotation) {
				reporter.add(this.graph, "loop_entry_violations", 1);
			} else if (error instanceof ExitNotXORAnnotation) {
				reporter.add(this.graph, "loop_exit_violations", 1);
			} else if (error instanceof NoStartAnnotation) {
				reporter.add(this.graph, "loop_without_entry", 1);
			}
		}

		/*String exportPath = Mojo.getExportPath();
		ArrayList<WorkflowGraph> graphs = new ArrayList<>();
		graphs.add(graph);
		graphs.addAll(decomposition.getDecomposition());
		WorkflowGraphExporter.exportToDot(graphs,
				 exportPath + File.separator,
				graph.hashCode() + ".dot");*/
	}

}