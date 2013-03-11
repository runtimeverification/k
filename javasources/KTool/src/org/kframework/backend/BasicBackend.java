package org.kframework.backend;

import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.sharing.AutomaticModuleImportsTransformer;
import org.kframework.compile.sharing.DittoFilter;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.FunctionalAdaptor;
import org.kframework.kil.Definition;
import org.kframework.main.FirstStep;
import org.kframework.main.LastStep;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.general.GlobalSettings;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/17/12 Time: 11:18 PM
 */
public abstract class BasicBackend implements Backend {
	protected Stopwatch sw;

	public ResolveConfigurationAbstraction getResolveConfigurationAbstraction() {
		return resolveConfigurationAbstraction;
	}

	public void setResolveConfigurationAbstraction(ResolveConfigurationAbstraction resolveConfigurationAbstraction) {
		this.resolveConfigurationAbstraction = resolveConfigurationAbstraction;
	}

	protected ResolveConfigurationAbstraction resolveConfigurationAbstraction;

	public BasicBackend(Stopwatch sw) {
		this.sw = sw;
	}

	@Override
	public Definition lastStep(Definition def) {
		return def;
	}

	@Override
	public Definition firstStep(Definition def) {
		return def;
	}

	public boolean autoinclude() {
		return true;
	}

	public CompilerSteps<Definition> getCompilationSteps() {
		CompilerSteps<Definition> steps = new CompilerSteps<Definition>();
		steps.add(new FirstStep(this));
		steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells()));
		steps.add(new RemoveBrackets());
		steps.add(new AddEmptyLists());
		steps.add(new CheckVisitorStep<Definition>(new CheckVariables()));
		steps.add(new CheckVisitorStep<Definition>(new CheckRewrite()));
		steps.add(new AutomaticModuleImportsTransformer());
		steps.add(new FunctionalAdaptor(new DittoFilter()));
		steps.add(new FlattenModules());
		steps.add(new StrictnessToContexts());
		steps.add(new FreezeUserFreezers());
		steps.add(new ContextsToHeating());
		steps.add(new AddSupercoolDefinition());
		steps.add(new AddHeatingConditions());
		steps.add(new AddSuperheatRules());
		steps.add(new DesugarStreams());
		steps.add(new ResolveFunctions());
		steps.add(new AddKCell());
		steps.add(new AddSymbolicK());
		if (GlobalSettings.symbolicEquality)
			steps.add(new AddSemanticEquality());
		// steps.add(new ResolveFresh());
		steps.add(new ResolveFreshMOS());
		steps.add(new AddTopCellConfig());
//		if (GlobalSettings.addTopCell) {
		steps.add(new AddTopCellRules());
//		}
//		steps.add(new AddEval());
		steps.add(new ResolveBinder());
		steps.add(new ResolveAnonymousVariables());
		steps.add(new ResolveBlockingInput());
		steps.add(new AddK2SMTLib());
		steps.add(new AddPredicates());
		steps.add(new ResolveSyntaxPredicates());
		steps.add(new ResolveBuiltins());
		steps.add(new ResolveListOfK());
		steps.add(new FlattenSyntax());
		steps.add(new AddKLabelToString());
		steps.add(new AddKLabelConstant());
		steps.add(new ResolveHybrid());
		resolveConfigurationAbstraction = new ResolveConfigurationAbstraction();
		steps.add(resolveConfigurationAbstraction);
		steps.add(new ResolveOpenCells());
		steps.add(new ResolveRewrite());
		steps.add(new SortCells(resolveConfigurationAbstraction));
		steps.add(new ResolveSupercool());
		steps.add(new AddStrictStar());
		steps.add(new AddDefaultComputational());
		steps.add(new AddOptionalTags());
		steps.add(new LastStep(this));
		return steps;
	}
}
