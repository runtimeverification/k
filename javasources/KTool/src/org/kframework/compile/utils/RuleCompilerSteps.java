package org.kframework.compile.utils;

import org.kframework.compile.transformers.AddKCell;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveSyntaxPredicates;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.ResolveContextAbstraction;
import org.kframework.compile.transformers.ResolveOpenCells;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;

public class RuleCompilerSteps extends CompilerSteps<Rule> {

	public RuleCompilerSteps(Definition def) {
		super();
		this.add(new AddKCell());
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
