package org.kframework.backend.java.symbolic;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.maude.MaudeBuiltinsFilter;
import org.kframework.backend.symbolic.TagUserRules;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.tags.AddDefaultComputational;
import org.kframework.compile.tags.AddOptionalTags;
import org.kframework.compile.tags.AddStrictStar;
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Bag;
import org.kframework.kil.*;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.api.KRun;
import org.kframework.main.FirstStep;
import org.kframework.main.LastStep;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/12/13 Time: 12:21 PM To change this template use File | Settings | File Templates.
 */
public class JavaSymbolicBackend extends BasicBackend {

	public static final String DEFINITION_FILENAME = "java_symbolic_definition.bin";

	public JavaSymbolicBackend(Stopwatch sw, org.kframework.kil.loader.Context context) {
		super(sw, context);
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
		MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(builtinsProperties, context);
		javaDef.accept(builtinsFilter);
		final String mainModule = javaDef.getMainModule();
		String builtins = "mod " + mainModule + "-BUILTINS is\n" + " including " + mainModule + "-BASE .\n" + builtinsFilter.getResult() + "endm\n";
		FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/builtins.maude", builtins);
		if (GlobalSettings.verbose)
			sw.printIntermediate("Generating equations for hooks");
		return super.firstStep(javaDef);
	}

	@Override
	public Definition lastStep(Definition javaDef) {
		try {
			OutputStream outputStream = new BufferedOutputStream(new FileOutputStream(JavaSymbolicBackend.DEFINITION_FILENAME));
			BinaryLoader.toBinary(javaDef, outputStream);
			outputStream.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

		Term term;
		List<Term> list1 = new ArrayList<Term>();
		list1.add(new Variable("B", "Bool"));
		list1.add(new Variable("S1", "Stmt"));
		list1.add(new Variable("S2", "Stmt"));
		Term kTerm = new KApp(KLabelConstant.of("'if(_)_else_", context), new KList(list1));
		List<Term> list2 = new ArrayList<Term>();
		list2.add(kTerm);
		Term kSequence = new KSequence(list2);
		// Term stateTerm = new Empty("Map");

		Bag bag = new Bag();
		bag.getContents().add(MetaK.wrap(kSequence, "k", Cell.Ellipses.NONE));
		// bag.getContents().add(MetaK.wrap(stateTerm, "state", Cell.Ellipses.NONE));
		Bag topBag = new Bag();
		topBag.getContents().add(MetaK.wrap(bag, "T", Cell.Ellipses.NONE));
		term = MetaK.wrap(topBag, MetaK.Constants.generatedTopCellLabel, Cell.Ellipses.NONE);

		try {
			term = (Term) term.accept(new FlattenSyntax(context));
		} catch (TransformerException e) {
			e.printStackTrace();
		}

		KRun kRun = new JavaSymbolicKRun(context);
		try {
			kRun.run(term);
		} catch (Exception e) {
			e.printStackTrace();
		}

		return javaDef;
	}

	@Override
	public void run(Definition javaDef) throws IOException {

		new MaudeBackend(sw, context).run(javaDef);

		String load = "load \"" + KPaths.getKBase(true) + KPaths.MAUDE_LIB_DIR + "/k-prelude\"\n";

		// load libraries if any
		String maudeLib = GlobalSettings.lib.equals("") ? "" : "load " + KPaths.windowfyPath(new File(GlobalSettings.lib).getAbsolutePath()) + "\n";
		load += maudeLib;

		final String mainModule = javaDef.getMainModule();
		// String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$",
		// "");

		String main = load + "load \"base.maude\"\n" + "load \"builtins.maude\"\n" + "mod " + mainModule + " is \n" + "  including " + mainModule + "-BASE .\n" + "  including " + mainModule
				+ "-BUILTINS .\n" + "  including K-STRICTNESS-DEFAULTS .\n" + "endm\n";
		FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/" + "main.maude", main);

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
		// FileUtil.saveInFile(context.dotk.getAbsolutePath()
		// + "/def-symbolic.xml", xml);
	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}

	@Override
	public CompilerSteps<Definition> getCompilationSteps() {
		CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
		steps.add(new FirstStep(this, context));

		/* sanity checks */
		steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
		steps.add(new CheckVisitorStep<Definition>(new CheckVariables(context), context));
		steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));

		/* syntactic macros */
		steps.add(new RemoveBrackets(context));
		steps.add(new AddEmptyLists(context));
		steps.add(new RemoveSyntacticCasts(context));

		/* module system */
		steps.add(new FlattenModules(context));

		/* strictness */
		steps.add(new StrictnessToContexts(context));
		steps.add(new FreezeUserFreezers(context));
		steps.add(new ContextsToHeating(context));
		// steps.add(new AddSupercoolDefinition());
		steps.add(new AddHeatingConditions(context));
		// steps.add(new AddSuperheatRules());
		// steps.add(new DesugarStreams());

		steps.add(new ResolveFunctions(context));
		steps.add(new AddKCell(context));
		steps.add(new AddTopCellRules(context));
		steps.add(new AddTopCellConfig(context));
		// steps.add(new AddSymbolicK());
		// steps.add(new ResolveFresh());
		// steps.add(new ResolveFreshMOS());

		// steps.add(new ResolveBinder());
		steps.add(new ResolveAnonymousVariables(context));
		// steps.add(new ResolveBlockingInput());
		// steps.add(new AddK2SMTLib());
		steps.add(new AddPredicates(context));
		//steps.add(new ResolveSyntaxPredicates());
		steps.add(new ResolveBuiltins(context));
		steps.add(new ResolveListOfK(context));
		steps.add(new FlattenSyntax(context));
		// steps.add(new AddKStringConversion());
		// steps.add(new AddKLabelConstant());
		steps.add(new ResolveHybrid(context));
		steps.add(new ResolveConfigurationAbstraction(new ConfigurationStructureMap(), context));
		steps.add(new ResolveOpenCells(context));
		steps.add(new ResolveRewrite(context));
		// steps.add(new ResolveSupercool());
		steps.add(new AddStrictStar(context));
		steps.add(new AddDefaultComputational(context));
		steps.add(new AddOptionalTags(context));

		/* tag with symbolic the rules that are not form k dist */
		steps.add(new TagUserRules(context));

		steps.add(new LastStep(this, context));

		return steps;
	}
}
