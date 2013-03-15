package org.kframework.compile.utils;

import org.kframework.compile.transformers.*;
import org.kframework.kil.Cell;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Variable;

import java.util.Map;

public class RuleCompilerSteps extends CompilerSteps<Rule> {

	public Map<Variable, Cell> getVariableMap() {
		return variableMap;
	}

	private final Map<Variable, Cell> variableMap;

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
		final SortCells sortCells = new SortCells(configurationStructureMap);
		variableMap = sortCells.getVariables();
		this.add(sortCells.getConfigurationTransformer());
	}
}
