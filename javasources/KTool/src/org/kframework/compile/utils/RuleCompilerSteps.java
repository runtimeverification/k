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
		ConfigurationStructureVisitor cfgStrVisitor = new ConfigurationStructureVisitor();
		def.accept(cfgStrVisitor);
		this.add(new ResolveContextAbstraction(cfgStrVisitor.getMaxLevel(), cfgStrVisitor.getConfig()));
		this.add(new ResolveOpenCells());
	}
}
