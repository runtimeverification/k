package org.kframework.backend.java.symbolic;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.maude.MaudeBuiltinsFilter;
import org.kframework.backend.symbolic.AddConditionToConfig;
import org.kframework.backend.symbolic.AddPathCondition;
import org.kframework.backend.symbolic.ReplaceConstants;
import org.kframework.backend.symbolic.TagUserRules;
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
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
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
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/12/13
 * Time: 12:21 PM
 * To change this template use File | Settings | File Templates.
 */
public class JavaSymbolicBackend extends BasicBackend {

    //public static String SYMBOLIC = "symbolic-kompile";

    public JavaSymbolicBackend(Stopwatch sw) {
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
    public Definition lastStep(Definition javaDef) {
        try {
            OutputStream outputStream = new BufferedOutputStream(new FileOutputStream("javadef"));
            BinaryLoader.toBinary(javaDef, outputStream);
            outputStream.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        try {
            InputStream inputStream = new BufferedInputStream(new FileInputStream("javadef"));
            javaDef = (Definition) BinaryLoader.fromBinary(inputStream);
            inputStream.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(javaDef);

        Term term;
        List<Term> list = new ArrayList<Term>();
        list.add(new Variable("B", "Bool"));
        list.add(new Variable("S1", "Stmt"));
        list.add(new Variable("S2", "Stmt"));
        Term kTerm = new KApp(Constant.KLABEL("'if`(_`)_else_"), new KList(list));
        Term stateTerm = new Empty("Map");

        Bag bag = new Bag();
        bag.getContents().add(MetaK.wrap(kTerm, "k", Cell.Ellipses.NONE));
        //bag.getContents().add(MetaK.wrap(stateTerm, "state", Cell.Ellipses.NONE));
        Bag topBag = new Bag();
        topBag.getContents().add(MetaK.wrap(bag, "T", Cell.Ellipses.NONE));
        term = MetaK.wrap(topBag, MetaK.Constants.generatedTopCellLabel, Cell.Ellipses.NONE);

        try {
            term = (Term) term.accept(new FlattenSyntax());
        } catch (TransformerException e) {
            e.printStackTrace();
        }

        symbolicRewriter.rewrite(term);

        return javaDef;
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

        System.err.println("ana are mere");

    }

    @Override
    public String getDefaultStep() {
        return "LastStep";
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>();
        steps.add(new FirstStep(this));

        /* sanity checks */
        steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells()));
        steps.add(new CheckVisitorStep<Definition>(new CheckVariables()));
        steps.add(new CheckVisitorStep<Definition>(new CheckRewrite()));

        /* syntactic macros */
        steps.add(new RemoveBrackets());
        steps.add(new AddEmptyLists());

        /* module system */
        steps.add(new AutomaticModuleImportsTransformer());
        steps.add(new FunctionalAdaptor(new DittoFilter()));
        steps.add(new FlattenModules());

        /* strictness */
        steps.add(new StrictnessToContexts());
        steps.add(new FreezeUserFreezers());
        steps.add(new ContextsToHeating());
        //steps.add(new AddSupercoolDefinition());
        steps.add(new AddHeatingConditions());
        //steps.add(new AddSuperheatRules());
        //steps.add(new DesugarStreams());

        steps.add(new ResolveFunctions());
        steps.add(new AddKCell());
        steps.add(new AddTopCellRules());
        steps.add(new AddTopCellConfig());
        //steps.add(new AddSymbolicK());
        //steps.add(new ResolveFresh());
        //steps.add(new ResolveFreshMOS());

        //steps.add(new AddEval());
        //steps.add(new ResolveBinder());
        steps.add(new ResolveAnonymousVariables());
        //steps.add(new ResolveBlockingInput());
        //steps.add(new AddK2SMTLib());
        steps.add(new AddPredicates());
        steps.add(new ResolveSyntaxPredicates());
        steps.add(new ResolveBuiltins());
        steps.add(new ResolveListOfK());
        steps.add(new FlattenSyntax());
        //steps.add(new AddKLabelToString());
        //steps.add(new AddKLabelConstant());
        steps.add(new ResolveHybrid());
        steps.add(new ResolveConfigurationAbstraction());
        steps.add(new ResolveOpenCells());
        steps.add(new ResolveRewrite());
        //steps.add(new ResolveSupercool());
        steps.add(new AddStrictStar());
        steps.add(new AddDefaultComputational());
        steps.add(new AddOptionalTags());

        /* tag with symbolic the rules that are not form k dist */
        steps.add(new TagUserRules());

        steps.add(new LastStep(this));

        return steps;
    }
}
