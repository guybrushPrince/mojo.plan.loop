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
import de.jena.uni.mojo.general.MajorPlan;
import de.jena.uni.mojo.model.WGNode;
import de.jena.uni.mojo.model.WorkflowGraph;
import de.jena.uni.mojo.plan.PreparationPlan;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.LoopDecomposition;
import de.jena.uni.mojo.plan.plugin.loop.decomposition.soundness.SoundnessLoopDecompositionAnalysis;
import de.jena.uni.mojo.util.export.WorkflowGraphExporter;
import de.jena.uni.mojo.util.store.ElementStore;

import java.io.File;
import java.util.ArrayList;

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
		this.errorList.addAll(preparationPlan.compute());
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
		this.errorList.addAll(decomposition.compute());

		reporter.put(this.graph, "ERRORS_DECOMPOSITION", this.errorList.size());

		/*String exportPath = Mojo.getExportPath();
		ArrayList<WorkflowGraph> graphs = new ArrayList<>();
		graphs.add(graph);
		graphs.addAll(decomposition.getDecomposition());
		WorkflowGraphExporter.exportToDot(graphs,
				 exportPath + File.separator,
				graph.hashCode() + ".dot");*/
	}

}