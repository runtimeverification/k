// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.maude.MaudeBuiltinsFilter;
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
import org.kframework.compile.transformers.*;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompileDataStructures;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.InitializeConfigurationStructure;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.main.FirstStep;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;

import java.io.File;
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

    public SymbolicBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    @Override
    public Definition firstStep(Definition javaDef) {
        String fileSep = System.getProperty("file.separator");
        String propPath = KPaths.getKBase(false) + fileSep + "lib" + fileSep + "maude" +
                fileSep;
        Properties specialMaudeHooks = new Properties();
        Properties maudeHooks = new Properties();
        try {
            FileUtil.loadProperties(maudeHooks, propPath + "MaudeHooksMap.properties");
            FileUtil.loadProperties(specialMaudeHooks, propPath + "SpecialMaudeHooks.properties");
        } catch (IOException e) {
            e.printStackTrace();
        }
        MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(maudeHooks, specialMaudeHooks, context);
        builtinsFilter.visitNode(javaDef);
        final String mainModule = javaDef.getMainModule();
        StringBuilder builtins = new StringBuilder().append("mod ")
            .append(mainModule).append("-BUILTINS is\n")
            .append(" including ").append(mainModule).append("-BASE .\n")
            .append(builtinsFilter.getResult()).append("endm\n");
        FileUtil.save(context.kompiled.getAbsolutePath() + "/builtins.maude", builtins);
        sw.printIntermediate("Generating equations for hooks");
        return super.firstStep(javaDef);
    }

    @Override
    public void run(Definition javaDef) {

        new MaudeBackend(sw, context).run(javaDef);

        String load = "load \"" + KPaths.getKBase(true) + KPaths.MAUDE_LIB_DIR + "/k-prelude\"\n";

        // load libraries if any
        String maudeLib = "".equals(options.experimental.lib) ? "" : "load " + KPaths.windowfyPath(new File(options.experimental.lib).getAbsolutePath()) + "\n";
        load += maudeLib;

        final String mainModule = javaDef.getMainModule();
        // String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$",
        // "");

        StringBuilder main = new StringBuilder().append(load).append("load \"base.maude\"\n")
            .append("load \"builtins.maude\"\n")
            .append("mod ").append(mainModule).append(" is \n")
            .append("  including ").append(mainModule).append("-BASE .\n")
            .append("  including ").append(mainModule).append("-BUILTINS .\n").append("endm\n");
        FileUtil.save(context.kompiled.getAbsolutePath() + "/" + "main.maude", main);

         UnparserFilter unparserFilter = new UnparserFilter(this.context);
         unparserFilter.visitNode(javaDef);

//        String unparsedText = unparserFilter.getResult();
//
//        System.out.println(unparsedText);
        //
        // XStream xstream = new XStream();
        // xstream.aliasPackage("k", "ro.uaic.info.fmse.k");
        //
        // String xml = xstream.toXML(def);
        //
        // FileUtil.save(context.dotk.getAbsolutePath()
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
        steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
        steps.add(new RemoveBrackets(context));
        steps.add(new AddEmptyLists(context));
        steps.add(new RemoveSyntacticCasts(context));
        steps.add(new CheckVisitorStep<Definition>(new CheckVariables(context), context));
        steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));
        steps.add(new FlattenModules(context));
        steps.add(new StrictnessToContexts(context));
        steps.add(new FreezeUserFreezers(context));
        steps.add(new ContextsToHeating(context));
        steps.add(new AddSupercoolDefinition(context));
        steps.add(new AddHeatingConditions(context));
        steps.add(new AddSuperheatRules(context));
        steps.add(new ResolveSymbolicInputStream(context)); // symbolic step
        steps.add(new DesugarStreams(context));
        steps.add(new ResolveFunctions(context));
        steps.add(new TagUserRules(context)); // symbolic step
        steps.add(new ReachabilityRuleToKRule(context)); // symbolic step
        steps.add(new AddKCell(context));
        steps.add(new AddSymbolicK(context));

        steps.add(new AddSemanticEquality(context));
        steps.add(new FreshCondToFreshVar(context));
        steps.add(new ResolveFreshVarMOS(context));
        steps.add(new AddTopCellConfig(context));
        steps.add(new AddConditionToConfig(context)); // symbolic step
        steps.add(new AddTopCellRules(context));
        steps.add(new ResolveBinder(context));
        steps.add(new ResolveAnonymousVariables(context));
        steps.add(new FlattenSyntax(context));
        steps.add(new ResolveBlockingInput(context));
        steps.add(new AddK2SMTLib(context));
        steps.add(new AddPredicates(context));
        steps.add(new ResolveSyntaxPredicates(context));
        steps.add(new ResolveBuiltins(context));
        steps.add(new ResolveListOfK(context));
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
        steps.add(new AddPathConditionToReachabilityKRule(context)); // symbolic step
        steps.add(new ResolveLtlAttributes(context)); // symbolic step (special case for ltl)

        steps.add(new ResolveSupercool(context));
        steps.add(new AddStrictStar(context));
        steps.add(new AddDefaultComputational(context));
        steps.add(new AddOptionalTags(context));
        steps.add(new DeclareCellLabels(context));

        return steps;
    }
}
