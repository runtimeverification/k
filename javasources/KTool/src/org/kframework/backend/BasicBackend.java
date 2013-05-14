package org.kframework.backend;

import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.sharing.DeclareCellLabels;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
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
	protected DefinitionHelper definitionHelper;

	public ConfigurationStructureMap getConfigurationStructureMap() {
		return configurationStructureMap;
	}

	public void setConfigurationStructureMap(ConfigurationStructureMap configurationStructureMap) {
		this.configurationStructureMap = configurationStructureMap;
	}

	private ConfigurationStructureMap configurationStructureMap;

	public BasicBackend(Stopwatch sw, DefinitionHelper definitionHelper) {
		this.sw = sw;
		this.definitionHelper = definitionHelper;
		configurationStructureMap = new ConfigurationStructureMap();
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
		CompilerSteps<Definition> steps = new CompilerSteps<Definition>(definitionHelper);
		steps.add(new FirstStep(this, definitionHelper));
		steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(definitionHelper), definitionHelper));
		steps.add(new RemoveBrackets(definitionHelper));
		steps.add(new AddEmptyLists(definitionHelper));
		steps.add(new RemoveSyntacticCasts(definitionHelper));
		steps.add(new CheckVisitorStep<Definition>(new CheckVariables(definitionHelper), definitionHelper));
		steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(definitionHelper), definitionHelper));
		steps.add(new FlattenModules(definitionHelper));
		steps.add(new StrictnessToContexts(definitionHelper));
		steps.add(new FreezeUserFreezers(definitionHelper));
		steps.add(new ContextsToHeating(definitionHelper));
		steps.add(new AddSupercoolDefinition(definitionHelper));
		steps.add(new AddHeatingConditions(definitionHelper));
		steps.add(new AddSuperheatRules(definitionHelper));
		steps.add(new DesugarStreams(definitionHelper));
		steps.add(new ResolveFunctions(definitionHelper));
		steps.add(new AddKCell(definitionHelper));
		steps.add(new AddSymbolicK(definitionHelper));
		if (GlobalSettings.symbolicEquality)
			steps.add(new AddSemanticEquality(definitionHelper));
		// steps.add(new ResolveFresh());
		steps.add(new FreshCondToFreshVar(definitionHelper));
		steps.add(new ResolveFreshVarMOS(definitionHelper));
		steps.add(new AddTopCellConfig(definitionHelper));
		if (GlobalSettings.addTopCell) {
		steps.add(new AddTopCellRules(definitionHelper));
		}
		steps.add(new ResolveBinder(definitionHelper));
		steps.add(new ResolveAnonymousVariables(definitionHelper));
		steps.add(new ResolveBlockingInput(definitionHelper));
		steps.add(new AddK2SMTLib(definitionHelper));
		steps.add(new AddPredicates(definitionHelper));
		steps.add(new ResolveSyntaxPredicates(definitionHelper));
		steps.add(new ResolveBuiltins(definitionHelper));
		steps.add(new ResolveListOfK(definitionHelper));
		steps.add(new FlattenSyntax(definitionHelper));
		steps.add(new AddKLabelToString(definitionHelper));
		steps.add(new AddKLabelConstant(definitionHelper));
		steps.add(new ResolveHybrid(definitionHelper));
		steps.add(new ResolveConfigurationAbstraction (configurationStructureMap, definitionHelper));
		steps.add(new ResolveOpenCells(definitionHelper));
		steps.add(new ResolveRewrite(definitionHelper));
		if (GlobalSettings.sortedCells) {
			steps.add(new SortCells(configurationStructureMap, definitionHelper));
		}
		steps.add(new ResolveSupercool(definitionHelper));
		steps.add(new AddStrictStar(definitionHelper));
		steps.add(new AddDefaultComputational(definitionHelper));
		steps.add(new AddOptionalTags(definitionHelper));
		steps.add(new DeclareCellLabels(definitionHelper));
		steps.add(new LastStep(this, definitionHelper));
		return steps;
	}
}
