package org.kframework.backend.symbolic;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Properties;

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
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.main.FirstStep;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class SymbolicBackend extends BasicBackend implements Backend {

	public static String SYMBOLIC = "symbolic-kompile";

	public SymbolicBackend(Stopwatch sw) {
		super(sw);
	}

	@Override
	public Definition firstStep(Definition javaDef) {
		String fileSep = System.getProperty("file.separator");
		String includePath = KPaths.getKBase(false) + fileSep + "include"
				+ fileSep + "maude" + fileSep;
		Properties builtinsProperties = new Properties();
		try {
			builtinsProperties.load(new FileInputStream(includePath
					+ "hooks.properties"));
		} catch (IOException e) {
			e.printStackTrace();
		}
		MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(
				builtinsProperties);
		javaDef.accept(builtinsFilter);
		final String mainModule = javaDef.getMainModule();
		String builtins = "mod " + mainModule + "-BUILTINS is\n"
				+ " including " + mainModule + "-BASE .\n"
				+ builtinsFilter.getResult() + "endm\n";
		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath()
				+ "/builtins.maude", builtins);
		if (GlobalSettings.verbose)
			sw.printIntermediate("Generating equations for hooks");
		return super.firstStep(javaDef);
	}

	@Override
	public void run(Definition javaDef) throws IOException {

		new MaudeBackend(sw).run(javaDef);

		String load = "load \"" + KPaths.getKBase(true)
				+ "/bin/maude/lib/k-prelude\"\n";

		// load libraries if any
		String maudeLib = GlobalSettings.lib.equals("") ? "" : "load "
				+ KPaths.windowfyPath(new File(GlobalSettings.lib)
						.getAbsolutePath()) + "\n";
		load += maudeLib;

		final String mainModule = javaDef.getMainModule();
		// String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$",
		// "");

		String main = load + "load \"base.maude\"\n"
				+ "load \"builtins.maude\"\n" + "mod " + mainModule + " is \n"
				+ "  including " + mainModule + "-BASE .\n" + "  including "
				+ mainModule + "-BUILTINS .\n"
				+ "  including K-STRICTNESS-DEFAULTS .\n" + "endm\n";
		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/"
				+ "main.maude", main);

//		 UnparserFilter unparserFilter = new UnparserFilter();
//		 javaDef.accept(unparserFilter);
//		
//		 String unparsedText = unparserFilter.getResult();
//		
//		 System.out.println(unparsedText);
		//
		// XStream xstream = new XStream();
		// xstream.aliasPackage("k", "ro.uaic.info.fmse.k");
		//
		// String xml = xstream.toXML(def);
		//
		// FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath()
		// + "/def-symbolic.xml", xml);

	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}

	@Override
	public CompilerSteps<Definition> getCompilationSteps() {
		CompilerSteps<Definition> steps = new CompilerSteps<Definition>();
		steps.add(new FirstStep(this));
		steps.add(new CheckVisitorStep<Definition>(
				new CheckConfigurationCells()));
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
		steps.add(new ResolveFreshVarMOS());
		steps.add(new AddTopCellConfig());
		steps.add(new AddConditionToConfig()); // symbolic step
		steps.add(new AddTopCellRules());
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
		steps.add(new TagUserRules());
		steps.add(new ReplaceConstants());
		steps.add(new AddPathCondition());
		steps.add(new ResolveSupercool());
		steps.add(new AddStrictStar());
		steps.add(new AddDefaultComputational());
		steps.add(new AddOptionalTags());

		return steps;
	}
}
