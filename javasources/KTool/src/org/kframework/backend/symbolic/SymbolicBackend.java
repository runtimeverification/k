package org.kframework.backend.symbolic;

import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.maude.MaudeBuiltinsFilter;
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
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.main.FirstStep;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;
/**
 * Compile a K definition symbolically, using both basic
 * and specific compilation steps. 
 * @author andreiarusoaie
 *
 */
public class SymbolicBackend extends BasicBackend implements Backend {

	public static String SYMBOLIC = "symbolic-kompile";
	public static String NOTSYMBOLIC = "not-symbolic-kompile";

	public SymbolicBackend(Stopwatch sw, DefinitionHelper definitionHelper) {
		super(sw, definitionHelper);
	}

	@Override
	public Definition firstStep(Definition javaDef) {
		String fileSep = System.getProperty("file.separator");
		String includePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "maude" + fileSep;
		Properties builtinsProperties = new Properties();
		try {
			builtinsProperties.load(new FileInputStream(includePath + "hooks.properties"));
		} catch (IOException e) {
			e.printStackTrace();
		}
		MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(builtinsProperties, definitionHelper);
		javaDef.accept(builtinsFilter);
		final String mainModule = javaDef.getMainModule();
		String builtins = "mod " + mainModule + "-BUILTINS is\n" + " including " + mainModule + "-BASE .\n" + builtinsFilter.getResult() + "endm\n";
		FileUtil.saveInFile(definitionHelper.dotk.getAbsolutePath() + "/builtins.maude", builtins);
		if (GlobalSettings.verbose)
			sw.printIntermediate("Generating equations for hooks");
		return super.firstStep(javaDef);
	}

	@Override
	public void run(Definition javaDef) throws IOException {

		new MaudeBackend(sw, definitionHelper).run(javaDef);

		String load = "load \"" + KPaths.getKBase(true) + "/bin/maude/lib/k-prelude\"\n";

		// load libraries if any
		String maudeLib = GlobalSettings.lib.equals("") ? "" : "load " + KPaths.windowfyPath(new File(GlobalSettings.lib).getAbsolutePath()) + "\n";
		load += maudeLib;

		final String mainModule = javaDef.getMainModule();
		// String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$",
		// "");

		String main = load + "load \"base.maude\"\n" + "load \"builtins.maude\"\n" + "mod " + mainModule + " is \n" + "  including " + mainModule + "-BASE .\n" + "  including " + mainModule
				+ "-BUILTINS .\n" + "  including K-STRICTNESS-DEFAULTS .\n" + "endm\n";
		FileUtil.saveInFile(definitionHelper.dotk.getAbsolutePath() + "/" + "main.maude", main);

		// UnparserFilter unparserFilter = new UnparserFilter();
		// javaDef.accept(unparserFilter);
		//
		// String unparsedText = unparserFilter.getResult();
		//
		// System.out.println(unparsedText);
		//
		// XStream xstream = new XStream();
		// xstream.aliasPackage("k", "ro.uaic.info.fmse.k");
		//
		// String xml = xstream.toXML(def);
		//
		// FileUtil.saveInFile(definitionHelper.dotk.getAbsolutePath()
		// + "/def-symbolic.xml", xml);

	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}

	@Override
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
		steps.add(new ResolveSymbolicInputStream(definitionHelper)); // symbolic step
		steps.add(new DesugarStreams(definitionHelper));
		steps.add(new ResolveFunctions(definitionHelper));
		steps.add(new TagUserRules(definitionHelper)); // symbolic step
		steps.add(new AddKCell(definitionHelper));
		steps.add(new AddSymbolicK(definitionHelper));

		steps.add(new AddSemanticEquality(definitionHelper));
		steps.add(new FreshCondToFreshVar(definitionHelper));
		steps.add(new ResolveFreshVarMOS(definitionHelper));
		steps.add(new AddTopCellConfig(definitionHelper));
		steps.add(new AddConditionToConfig(definitionHelper)); // symbolic step
		steps.add(new AddTopCellRules(definitionHelper));
		steps.add(new AddEval(definitionHelper));
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
		steps.add(new ResolveConfigurationAbstraction(new ConfigurationStructureMap(), definitionHelper));
		steps.add(new ResolveOpenCells(definitionHelper));
		steps.add(new ResolveRewrite(definitionHelper));
		// steps.add(new LineariseTransformer()); //symbolic step
		steps.add(new ReplaceConstants(definitionHelper)); // symbolic step
		steps.add(new AddPathCondition(definitionHelper)); // symbolic step
		steps.add(new ResolveSupercool(definitionHelper));
		steps.add(new AddStrictStar(definitionHelper));
		steps.add(new AddDefaultComputational(definitionHelper));
		steps.add(new AddOptionalTags(definitionHelper));
		steps.add(new DeclareCellLabels(definitionHelper));
		steps.add(new AddOptionalTags(definitionHelper));

		return steps;
	}
}
