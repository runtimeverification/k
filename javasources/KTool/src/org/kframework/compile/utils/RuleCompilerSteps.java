package org.kframework.compile.utils;

import org.kframework.compile.transformers.*;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;

public class RuleCompilerSteps extends CompilerSteps<Rule> {

	private final SortCells cellSorter;

	public Term getCellFragment(Variable v) {
		return cellSorter.getCellFragment(v);
	}

	public RuleCompilerSteps(Definition def) {
		super();
		this.add(new AddKCell());
		this.add(new AddTopCellRules());
		this.add(new ResolveAnonymousVariables());
		this.add(new ResolveSyntaxPredicates());
		this.add(new ResolveListOfK());
		this.add(new FlattenSyntax());
		ConfigurationStructureMap configurationStructureMap = new
				ConfigurationStructureMap();
		ConfigurationStructureVisitor cfgStrVisitor =
				new ConfigurationStructureVisitor(configurationStructureMap);
		def.accept(cfgStrVisitor);
		final ResolveContextAbstraction resolveContextAbstraction =
				new ResolveContextAbstraction(cfgStrVisitor.getMaxLevel(),
						configurationStructureMap);
		this.add(resolveContextAbstraction);
		this.add(new ResolveOpenCells());
		cellSorter = new SortCells(configurationStructureMap);
		this.add(cellSorter.getConfigurationTransformer());
	}
}
