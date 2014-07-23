// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.maude.MaudeBuiltinsFilter;
import org.kframework.backend.maude.krun.MaudeKRun;
import org.kframework.backend.symbolic.AddConditionToConfig;
import org.kframework.backend.symbolic.AddPathCondition;
import org.kframework.backend.symbolic.ReplaceConstants;
import org.kframework.backend.symbolic.TagUserRules;
import org.kframework.backend.unparser.UnparserFilter;
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
import org.kframework.compile.transformers.AddKStringConversion;
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
import org.kframework.compile.utils.CompileDataStructures;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.InitializeConfigurationStructure;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kcheck.utils.AddCheckConstants;
import org.kframework.kcheck.utils.AddCircularityRules;
import org.kframework.kcheck.utils.AddImplicationRules;
import org.kframework.kcheck.utils.AddPathConditionToCircularities;
import org.kframework.kcheck.utils.AddPathConditionToImplications;
import org.kframework.kcheck.utils.GeneratePrograms;
import org.kframework.kcheck.utils.MergeToTransformer;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.main.FirstStep;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;

public class RLBackend extends BasicBackend implements Backend {

    public static int idx = 5000;

    // the set of reachability rules
    List<ASTNode> reachabilityRules = null;

    // the parsed initial program
    private Term program = null;

    public static final String INTERNAL_KLABEL = "rrcondition";
    public static final String SIMPLIFY_KLABEL = "'simplifyBool";
    public static boolean SIMPLIFY = false;

    // cmd line option
    public static String PGM = null;

    // the list of final programs
    List<Term> programs;

    // left generated programs
    private List<Term> lpgms = null;
    // initial context
    private Term icontext = null;

    public RLBackend(Stopwatch sw, Context context) {
        super(sw, context);
        reachabilityRules = new ArrayList<ASTNode>();
        programs = new ArrayList<Term>();
    }

    @Override
    public Definition firstStep(Definition javaDef) {
        String fileSep = System.getProperty("file.separator");
        String propPath = KPaths.getKBase(false) + fileSep + "lib" + fileSep
                + "maude" + fileSep;
        Properties specialMaudeHooks = new Properties();
        Properties maudeHooks = new Properties();
        try {
            FileUtil.loadProperties(maudeHooks, propPath + "MaudeHooksMap.properties");
            FileUtil.loadProperties(specialMaudeHooks, propPath + "SpecialMaudeHooks.properties");
        } catch (IOException e) {
            e.printStackTrace();
        }
        MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(
                maudeHooks, specialMaudeHooks, context);
        builtinsFilter.visitNode(javaDef);
        final String mainModule = javaDef.getMainModule();
        StringBuilder builtins = new StringBuilder().append("mod ")
            .append(mainModule).append("-BUILTINS is\n")
            .append(" including ").append(mainModule).append("-BASE .\n")
            .append(builtinsFilter.getResult()).append("endm\n");
        FileUtil.save(context.dotk.getAbsolutePath() + "/builtins.maude",
            builtins);
        sw.printIntermediate("Generating equations for hooks");
        return super.firstStep(javaDef);
    }

    @Override
    public void run(Definition javaDef) {

        /******************************
         * initial setup of definition *
         *******************************/
        new MaudeBackend(sw, context).run(javaDef);

        String load = "load \"" + KPaths.getKBase(true) + KPaths.MAUDE_LIB_DIR
                + "/k-prelude\"\n";

        // load libraries if any
        //String maudeLib = GlobalSettings.lib.equals("") ? "" : "load "
        //        + KPaths.windowfyPath(new File(GlobalSettings.lib)
        //                .getAbsolutePath()) + "\n";
        //load += maudeLib;

        final String mainModule = javaDef.getMainModule();
        // String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$",
        // "");

        StringBuilder main = new StringBuilder().append(load).append("load \"base.maude\"\n")
            .append("load \"builtins.maude\"\n")
            .append("mod ").append(mainModule).append(" is \n")
            .append("  including ").append(mainModule).append("-BASE .\n")
            .append("  including ").append(mainModule).append("-BUILTINS .\n").append("endm\n");
        FileUtil.save(context.dotk.getAbsolutePath() + "/" + "main.maude", main);
        context.kompiled = context.dotk;
        /****************
         * end *
         ****************/

        UnparserFilter unparserFilter = new UnparserFilter(context);
        unparserFilter.visitNode(javaDef);

        String unparsedText = unparserFilter.getResult();

        FileUtil.save(".symbolic.k", unparsedText);
        // System.exit(1);

        /****************************
         * initial setup of krun *
         *****************************/
        //K.compiled_def = context.dotk.getAbsolutePath();
        //K.main_module = mainModule;
        //K.init(context);
        // delete temporary krun directory
//        deleteDirectory(new File(K.krunDir));
//        Runtime.getRuntime().addShutdownHook(new Thread() {
//            public void run() {
//                try {
//                    moveDirectory(new File(K.krunTempDir), new File(K.krunDir));
//                } catch (IOException e) {
//                    e.printStackTrace();
//                }
//            }
//        });
        Rule defaultPattern = null;
        RuleCompilerSteps defaultPatternInfo = null;
        ASTNode pattern;
        try {
            pattern = DefinitionLoader.parsePattern(
                    null, //K.pattern,
                    "Command line pattern",
                    Sort.BAG.name(),
                    context);
            //defaultPatternInfo = new RuleCompilerSteps(javaDef, context);
            pattern = defaultPatternInfo.compile(new Rule((Sentence) pattern),
                    null);
            defaultPattern = (Rule) pattern;
        } catch (ParseFailedException e1) {
            e1.report();
        } catch (CompilerStepDone e) {
            e.printStackTrace();
        }

        // setup the runner
        MaudeKRun mkr = null;//new MaudeKRun(context, Stopwatch.instance());
        mkr.setBackendOption("io", false);
        /****************
         * end *
         ****************/

        /********************
         * initial context *
         ********************/
        // setup initial context
        //K.kompiled_cfg = (org.kframework.kil.Configuration)
        //    BinaryLoader.load(K.compiled_def + "/configuration.bin");
        if (PGM != null) {
            RunProcess rp = new RunProcess();
            //try {
                //KRunResult<KRunState> res = mkr.run(Main.makeConfiguration(
                //        program, null, rp, false, context));
                //icontext = res.getResult().getRawResult();//.getResult();
            //} catch (KRunExecutionException e1) {
            //    e1.printStackTrace();
            //}
        }
        /****************
         * end *
         ****************/

        /****************
         * merge *
         ****************/
        if (icontext != null) {
            for (Term lpgm : lpgms) {
                Term merged;
                merged = mergeLeftIntoRight(lpgm, icontext);
//                    System.out.println("Left: " + lpgm);
//                    System.out.println("Right:" + icontext);
//                    System.out.println("Merged: " + merged);
                programs.add(merged);
//                programs.add(merged);
            }
        } else {
            programs = lpgms;
        }

//        System.exit(1);

        // prints programs when verbose
        //if (GlobalSettings.verbose) {
            for (int i = 0; i < programs.size(); i++)
                System.out.println("PGM(" + i + "): " + programs.get(i));
        //}

        for (Term pgm : programs) {
            try {
                System.out.println("Verifying PGM(" + programs.indexOf(pgm)
                        + ") ...");
                // System.out.println("PGM: " + pgm);
                KRunResult<SearchResults> result = mkr.search(null, null,
                        SearchType.FINAL, defaultPattern, pgm,
                        defaultPatternInfo);
                System.out.println("Result: " + result + "\n\n");
            } catch (KRunExecutionException e) {
                e.printStackTrace();
            }
        }
    }

    private Term mergeLeftIntoRight(Term lpgm, Term icontext) {

        Term context = icontext.shallowCopy();
        MergeToTransformer mtt = new MergeToTransformer(this.context, lpgm);
        context = (Term) mtt.visitNode(context);

        return context;
    }

    @Override
    public String getDefaultStep() {
        return "LastStep";
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
        steps.add(new FirstStep(this, context));

        steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(
                context), context));
        steps.add(new RemoveBrackets(context));
        steps.add(new AddEmptyLists(context));
        steps.add(new RemoveSyntacticCasts(context));
        steps.add(new CheckVisitorStep<Definition>(new CheckVariables(context),
                context));
        steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(context),
                context));
        steps.add(new FlattenModules(context));
        steps.add(new StrictnessToContexts(context));
        steps.add(new FreezeUserFreezers(context));
        steps.add(new ContextsToHeating(context));
        steps.add(new AddSupercoolDefinition(context));
        steps.add(new AddHeatingConditions(context));
        steps.add(new AddSuperheatRules(context));
        // steps.add(new ResolveSymbolicInputStream(context)); // symbolic step
        steps.add(new DesugarStreams(context));
        steps.add(new ResolveFunctions(context));
        steps.add(new TagUserRules(context)); // symbolic step
        steps.add(new AddKCell(context));
        steps.add(new AddSymbolicK(context));

        ResolveRLFile rl = new ResolveRLFile(context, PGM);
        reachabilityRules = rl.getReachabilityRules();
        program = rl.getPgm();

        steps.add(new AddCheckConstants(context, reachabilityRules.size()));
        steps.add(new AddCircularityRules(context, reachabilityRules));
        steps.add(new AddImplicationRules(context, reachabilityRules));

        steps.add(new AddSemanticEquality(context));
        steps.add(new FreshCondToFreshVar(context));
        steps.add(new ResolveFreshVarMOS(context));
        steps.add(new AddTopCellConfig(context));
        AddConditionToConfig.PC = false;
        steps.add(new AddConditionToConfig(context)); // symbolic step
        steps.add(new AddTopCellRules(context));
        steps.add(new ResolveBinder(context));
        steps.add(new ResolveAnonymousVariables(context));
        steps.add(new ResolveBlockingInput(context));
        steps.add(new AddK2SMTLib(context));
        steps.add(new AddPredicates(context));
        steps.add(new ResolveSyntaxPredicates(context));
        steps.add(new ResolveBuiltins(context));
        steps.add(new ResolveListOfK(context));
        steps.add(new FlattenSyntax(context));
        steps.add(new InitializeConfigurationStructure(context));
        steps.add(new AddKStringConversion(context));
        steps.add(new AddKLabelConstant(context));
        steps.add(new ResolveHybrid(context));

        steps.add(new ResolveConfigurationAbstraction(context));
        steps.add(new ResolveOpenCells(context));
        steps.add(new ResolveRewrite(context));
        steps.add(new CompileDataStructures(context));

        // steps.add(new LineariseTransformer()); // symbolic step
        steps.add(new ReplaceConstants(context)); // symbolic step
        steps.add(new AddPathCondition(context)); // symbolic step

        steps.add(new AddPathConditionToCircularities(context,
                reachabilityRules));
        steps.add(new AddPathConditionToImplications(context, reachabilityRules));
        GeneratePrograms gp = new GeneratePrograms(context, reachabilityRules);
        steps.add(gp);
        lpgms = gp.getPrograms();

        steps.add(new ResolveSupercool(context));
        steps.add(new AddStrictStar(context));
        steps.add(new AddDefaultComputational(context));
        steps.add(new AddOptionalTags(context));
        steps.add(new DeclareCellLabels(context));

        return steps;
    }
}
