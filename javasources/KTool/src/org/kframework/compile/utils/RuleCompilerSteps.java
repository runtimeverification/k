package org.kframework.compile.utils;

import org.kframework.compile.transformers.*;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;

public class RuleCompilerSteps extends CompilerSteps<Rule> {

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
		this.add(new SortCells(configurationStructureMap).getConfigurationTransformer());
	}
}
