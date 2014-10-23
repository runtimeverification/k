// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.FirstStep;
import org.kframework.backend.LastStep;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.checks.CheckConfigurationCells;
import org.kframework.compile.checks.CheckRewrite;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.compile.sharing.DeclareCellLabels;
import org.kframework.compile.sharing.FreshVariableNormalizer;
import org.kframework.compile.sharing.SortRulesNormalizer;
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
import org.kframework.compile.transformers.AddStreamCells;
import org.kframework.compile.transformers.AddSupercoolDefinition;
import org.kframework.compile.transformers.AddSuperheatRules;
import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.compile.transformers.AddTopCellRules;
import org.kframework.compile.transformers.Cell2DataStructure;
import org.kframework.compile.transformers.ContextsToHeating;
import org.kframework.compile.transformers.DeleteFunctionRules;
import org.kframework.compile.transformers.DesugarStreams;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.FreezeUserFreezers;
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
import org.kframework.compile.transformers.SetVariablesInferredSort;
import org.kframework.compile.transformers.StrictnessToContexts;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.compile.utils.CompileDataStructures;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.InitializeConfigurationStructure;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringBuilderUtil;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import com.google.inject.Inject;

import java.io.IOException;
import java.util.Properties;

public class KompileBackend extends BasicBackend {

    private final FileUtil files;
    private final KExceptionManager kem;

    @Inject
    KompileBackend(Stopwatch sw, Context context, FileUtil files, KExceptionManager kem) {
        super(sw, context);
        this.files = files;
        this.kem = kem;
    }

    @Override
    public Definition firstStep(Definition javaDef) {
        Properties specialMaudeHooks = new Properties();
        Properties maudeHooks = new Properties();
        try {
            FileUtil.loadProperties(maudeHooks, getClass(), "MaudeHooksMap.properties");
            FileUtil.loadProperties(specialMaudeHooks, getClass(), "SpecialMaudeHooks.properties");
        } catch (IOException e) {
            e.printStackTrace();
        }
        MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(maudeHooks, specialMaudeHooks, context, kem);
        builtinsFilter.visitNode(javaDef);
        final String mainModule = javaDef.getMainModule();
        StringBuilder builtins = new StringBuilder()
            .append("mod ").append(mainModule).append("-BUILTINS is\n").append(" including ")
            .append(mainModule).append("-BASE .\n")
            .append(builtinsFilter.getResult()).append("endm\n");

        files.saveToKompiled("builtins.maude", builtins.toString());
        sw.printIntermediate("Generating equations for hooks");
        javaDef = (Definition) new DeleteFunctionRules(maudeHooks.stringPropertyNames(), context)
            .visitNode(javaDef);
        return super.firstStep(javaDef);
    }

    @Override
    public void run(Definition javaDef) {
        javaDef = (Definition) new FreshVariableNormalizer(context).visitNode(javaDef);
        javaDef = (Definition) new SortRulesNormalizer(context).visitNode(javaDef);
        MaudeFilter maudeFilter = new MaudeFilter(context, kem);
        maudeFilter.visitNode(javaDef);

        final String mainModule1 = javaDef.getMainModule();
        StringBuilder maudified = maudeFilter.getResult();
        StringBuilderUtil.replaceFirst(maudified, mainModule1, mainModule1 + "-BASE");

        files.saveToKompiled("base.maude", maudified.toString());
        sw.printIntermediate("Generating Maude file");

        String load = "load \"" + JarInfo.getKBase(true) + JarInfo.MAUDE_LIB_DIR + "/k-prelude\"\n";

        final String mainModule = javaDef.getMainModule();
        //String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$", "");

        StringBuilder main = new StringBuilder().append(load).append("load \"base.maude\"\n")
            .append("load \"builtins.maude\"\n").append("mod ").append(mainModule).append(" is \n")
            .append("  including ").append(mainModule).append("-BASE .\n")
            .append("  including ").append(mainModule).append("-BUILTINS .\n")
            .append("eq mainModule = '").append(mainModule).append(" .\nendm\n");
        files.saveToKompiled("main.maude", main.toString());
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        CompilerSteps<Definition> steps = new CompilerSteps<Definition>(context);
        steps.add(new FirstStep(this, context));
        steps.add(new CheckVisitorStep<Definition>(new CheckConfigurationCells(context), context));
        steps.add(new RemoveBrackets(context));
        steps.add(new SetVariablesInferredSort(context));
        steps.add(new AddEmptyLists(context, kem));
        steps.add(new RemoveSyntacticCasts(context));
//        steps.add(new EnforceInferredSorts(context));
        steps.add(new CheckVisitorStep<Definition>(new CheckVariables(context, kem), context));
        steps.add(new CheckVisitorStep<Definition>(new CheckRewrite(context), context));
        steps.add(new FlattenModules(context, kem));
        steps.add(new StrictnessToContexts(context));
        steps.add(new FreezeUserFreezers(context));
        steps.add(new ContextsToHeating(context));
        steps.add(new AddSupercoolDefinition(context));
        steps.add(new AddHeatingConditions(context));
        steps.add(new AddSuperheatRules(context));
        steps.add(new DesugarStreams(context));
        steps.add(new ResolveFunctions(context));
        steps.add(new AddKCell(context));
        steps.add(new AddStreamCells(context));
        steps.add(new AddSymbolicK(context));
        steps.add(new AddSemanticEquality(context));
        steps.add(new ResolveFreshVarMOS(context));
        steps.add(new AddTopCellConfig(context));
        if (options.experimental.addTopCell) {
            steps.add(new AddTopCellRules(context));
        }
        steps.add(new ResolveBinder(context));
        steps.add(new ResolveAnonymousVariables(context));
        steps.add(new AddK2SMTLib(context));
        steps.add(new AddPredicates(context));
        steps.add(new ResolveSyntaxPredicates(context));
        steps.add(new ResolveBuiltins(context));
        steps.add(new ResolveListOfK(context));
        steps.add(new FlattenSyntax(context));
        steps.add(new ResolveBlockingInput(context, kem));
        steps.add(new InitializeConfigurationStructure(context));
        steps.add(new AddKStringConversion(context));
        steps.add(new AddKLabelConstant(context));
        steps.add(new ResolveHybrid(context));
        steps.add(new ResolveConfigurationAbstraction (context, kem));
        steps.add(new ResolveOpenCells(context));
        steps.add(new ResolveRewrite(context));
        steps.add(new CompileDataStructures(context, kem));
        steps.add(new Cell2DataStructure(context));
        steps.add(new ResolveSupercool(context));
        steps.add(new AddStrictStar(context));
        steps.add(new AddDefaultComputational(context));
        steps.add(new AddOptionalTags(context));
        steps.add(new DeclareCellLabels(context));
        steps.add(new LastStep(this, context));
        return steps;
    }

    @Override
    public String getDefaultStep() {
        return "LastStep";
    }

    @Override
    public boolean documentation() {
        return false;
    }

    @Override
    public boolean generatesDefinition() {
        return true;
    }

}
