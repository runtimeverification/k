package org.kframework.backend;

import org.kframework.compile.AddEval;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.sharing.DeclareCellLabels;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.AddHeatingConditions;
import org.kframework.compile.transformers.AddK2SMTLib;
import org.kframework.compile.transformers.AddKCell;
import org.kframework.compile.transformers.AddKLabelConstant;
import org.kframework.compile.transformers.AddKLabelToString;
import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.transformers.AddSemanticEquality;
import org.kframework.compile.transformers.AddSupercoolDefinition;
import org.kframework.compile.transformers.AddSuperheatRules;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.compile.transformers.AddTopCellRules;
import org.kframework.compile.transformers.ContextsToHeating;
import org.kframework.compile.transformers.DesugarStreams;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.FreezeUserFreezers;
import org.kframework.compile.transformers.FreshCondToFreshVar;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.transformers.ResolveAnonymousVariables;
import org.kframework.compile.transformers.ResolveBinder;
import org.kframework.compile.transformers.ResolveBlockingInput;
import org.kframework.compile.transformers.ResolveBuiltins;
import org.kframework.compile.transformers.ResolveFreshVarMOS;
import org.kframework.compile.transformers.ResolveFunctions;
import org.kframework.compile.transformers.ResolveHybrid;
import org.kframework.compile.transformers.ResolveListOfK;
import org.kframework.compile.transformers.ResolveOpenCells;
import org.kframework.compile.transformers.ResolveRewrite;
import org.kframework.compile.transformers.ResolveSupercool;
import org.kframework.compile.transformers.ResolveSyntaxPredicates;
import org.kframework.compile.transformers.StrictnessToContexts;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerSteps;
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
		steps.add(new RemoveSyntacticCasts());
		steps.add(new CheckVisitorStep<Definition>(new CheckVariables()));
		steps.add(new CheckVisitorStep<Definition>(new CheckRewrite()));
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
		steps.add(new FreshCondToFreshVar());
		steps.add(new ResolveFreshVarMOS());
		steps.add(new AddTopCellConfig());
		if (GlobalSettings.addTopCell) {
			steps.add(new AddTopCellRules());
		}
		steps.add(new AddEval());
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
		steps.add(new ResolveConfigurationAbstraction());
		steps.add(new ResolveOpenCells());
		steps.add(new ResolveRewrite());
		steps.add(new ResolveSupercool());
		steps.add(new AddStrictStar());
		steps.add(new AddDefaultComputational());
		steps.add(new AddOptionalTags());
		steps.add(new DeclareCellLabels());
		steps.add(new LastStep(this));
		return steps;
	}
}
