// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.compile.checks.CheckListDecl;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.compile.checks.CheckSyntaxDecl;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.AddAutoIncludedModulesVisitor;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectModuleImportsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.RemoveUnusedModules;
import org.kframework.parser.generator.ParsersPerModule;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.parser.concrete.DefinitionLocalKParser;
import org.kframework.parser.concrete.disambiguate.NormalizeASTTransformer;
import org.kframework.parser.generator.OuterParser;
import org.kframework.parser.generator.CacheLookupFilter;
import org.kframework.parser.generator.Definition2SDF;
import org.kframework.parser.generator.DefinitionSDF;
import org.kframework.parser.generator.DisambiguateRulesFilter;
import org.kframework.parser.generator.ParseConfigsFilter;
import org.kframework.parser.generator.ParseRulesFilter;
import org.kframework.parser.generator.ProgramSDF;
import org.kframework.parser.utils.CachedSentence;
import org.kframework.parser.utils.ResourceExtractor;
import org.kframework.parser.utils.Sdf2Table;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class DefinitionLoader {

    private final Stopwatch sw;
    private final BinaryLoader loader;
    private final KExceptionManager kem;
    private final OuterParser outer;
    private final boolean autoinclude;
    private final FileUtil files;
    private final Sdf2Table sdf2Table;

    @Inject
    public DefinitionLoader(
            Stopwatch sw,
            BinaryLoader loader,
            KExceptionManager kem,
            OuterParser outer,
            @Backend.Autoinclude boolean autoinclude,
            FileUtil files,
            Sdf2Table sdf2Table) {
        this.sw = sw;
        this.loader = loader;
        this.kem = kem;
        this.outer = outer;
        this.autoinclude = autoinclude;
        this.files = files;
        this.sdf2Table = sdf2Table;
    }

    public Definition loadDefinition(File mainFile, String lang, Context context) {
        Definition javaDef;
        File canoFile = mainFile.getAbsoluteFile();

        String extension = FilenameUtils.getExtension(mainFile.getAbsolutePath());
        if ("bin".equals(extension)) {
            javaDef = loader.loadOrDie(Definition.class, canoFile);

            sw.printIntermediate("Load definition from binary");

            javaDef.preprocess(context, autoinclude);

            sw.printIntermediate("Preprocess");

        } else {
            javaDef = parseDefinition(mainFile, lang, context);
        }
        return javaDef;
    }

    /**
     * step. 1. slurp 2. gen files 3. gen TBLs 4. import files in stratego 5. parse configs 6. parse rules 7. ???
     *
     * @param mainFile
     * @param mainModule
     * @return
     */
    public Definition parseDefinition(File mainFile, String mainModule, Context context) {
        // for now just use this file as main argument
        // ------------------------------------- outer parsing

        outer.slurp(mainFile.getPath(), context);

        // transfer information from the OuterParser object, to the Definition object
        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        try {
            def.setMainFile(mainFile.getCanonicalFile());
        } catch (IOException e) {
            // this isn't worth crashing the application over, so just use the absolute path
            def.setMainFile(mainFile.getAbsoluteFile());
        }
        def.setMainModule(mainModule);
        def.getDefinitionContext().addModules(outer.getModulesMap().values());
        def.setItems(outer.getModuleItems());

        if (!def.getDefinitionContext().containsModule(context.kompileOptions.syntaxModule())) {
            String msg = "Could not find main syntax module used to generate a parser for programs (X-SYNTAX). Using: '" + mainModule + "' instead.";
            kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.INNER_PARSER, msg));
            def.setMainSyntaxModule(mainModule);
        } else {
            def.setMainSyntaxModule(context.kompileOptions.syntaxModule());
        }

        if (!def.getDefinitionContext().containsModule(mainModule)) {
            String msg = "Could not find main module '" + mainModule + "'. Use --main-module option to specify another.";
            throw KExceptionManager.compilerError(msg);
        }
        sw.printIntermediate("Outer Parsing");

        if(autoinclude)
            new AddAutoIncludedModulesVisitor(context).visitNode(def);

        def = (Definition) new RemoveUnusedModules(context, autoinclude).visitNode(def);

        // new CheckModulesAndFilesImportsDecl(context).visitNode(def);
        new CollectModuleImportsVisitor(context).visitNode(def);

        def.preprocess(context, autoinclude);

        sw.printIntermediate("Preprocess");

        new CheckVisitorStep<Definition>(new CheckSyntaxDecl(context, kem), context).check(def);
        new CheckVisitorStep<Definition>(new CheckListDecl(context), context).check(def);
        new CheckVisitorStep<Definition>(new CheckSortTopUniqueness(context), context).check(def);

        sw.printIntermediate("Checks");

        if (context.kompileOptions.experimental.javaParser) {
            // save the new parser info
            Grammar newParserGrammar = ProgramSDF.getNewParserForPrograms(def, context, kem);
            loader.saveOrDie(files.resolveKompiled("newParser.bin"), newParserGrammar);

            Map<String, Grammar> parsers = ParsersPerModule.generateParsersForModules(def, context, kem);
            // save the new parser info for all modules. This should make the previous call obsolete (soon)
            loader.saveOrDie(context.files.resolveKompiled("newModuleParsers.bin"), parsers);
            sw.printIntermediate("Gen module parsers");
        }

        File cache = files.resolveKompiled("defx-cache.bin");
        Thread t2 = null;
        if (!context.kompileOptions.experimental.javaParserRules) {
            // ------------------------------------- generate files
            DefinitionLocalKParser.init(files.resolveKompiled("."));
            ResourceExtractor.ExtractDefSDF(files.resolveTemp("def"));
            ResourceExtractor.ExtractGroundSDF(files.resolveTemp("ground"));

            ResourceExtractor.ExtractProgramSDF(files.resolveTemp("pgm"));
            // ------------------------------------- generate parser TBL
            // cache the TBL if the sdf file is the same
            String oldSdfPgm = "";
            if (files.resolveKompiled("Program.sdf").exists())
                oldSdfPgm = files.loadFromKompiled("Program.sdf");

            StringBuilder newSdfPgmBuilder = ProgramSDF.getSdfForPrograms(def, context, kem);

            String newSdfPgm = newSdfPgmBuilder.toString();
            files.saveToTemp("pgm/Program.sdf", newSdfPgm);

            sw.printIntermediate("File Gen Pgm");

            if (!oldSdfPgm.equals(newSdfPgm) || !files.resolveKompiled("Program.tbl").exists()) {
                sdf2Table.run_sdf2table(files.resolveTemp("pgm"), "Program");
                files.copyTempFileToKompiledDirectory("pgm/Program.sdf");
                files.copyTempFileToKompiledDirectory("pgm/Program.tbl");
                sw.printIntermediate("Generate TBLPgm");
            }

            // ------------------------------------- generate parser TBL
            // cache the TBL if the sdf file is the same
            String oldSdf = "";
            if (files.resolveKompiled("Integration.sdf").exists())
                oldSdf = files.loadFromKompiled("Integration.sdf");
            String newSdf = DefinitionSDF.getSdfForDefinition(def, context).toString();
            files.saveToTemp("def/Integration.sdf", newSdf);
            files.saveToTemp("ground/Integration.sdf", Definition2SDF.getSdfForDefinition(def, context).toString());

            sw.printIntermediate("File Gen Def");

            if (!oldSdf.equals(newSdf) || !files.resolveKompiled("Rule.tbl").exists()
                    || !files.resolveKompiled("Ground.tbl").exists()) {
                try {
                    // delete the file with the cached/partially parsed rules
                    if (cache.exists() && !cache.delete()) {
                        throw KExceptionManager.criticalError("Could not delete file " + cache);
                    }
                    // Sdf2Table.run_sdf2table(new File(context.dotk.getAbsoluteFile() + "/def"), "Concrete");
                    Thread t1 = sdf2Table.run_sdf2table_parallel(files.resolveTemp("def"), "Concrete");
                    t2 = sdf2Table.run_sdf2table_parallel(files.resolveTemp("ground"), "Concrete");
                    t1.join();
                    files.copyTempFileToKompiledDirectory("def/Integration.sdf");
                    files.copyTempFileToKompiledFile("def/Concrete.tbl", "Rule.tbl");
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    throw KExceptionManager.criticalError(
                            "Thread was interrupted trying to run SDF2Table");
                }


                sw.printIntermediate("Generate TBLDef");
            }
        }

        def = (Definition) new ParseConfigsFilter(context, kem).visitNode(def);
        new CollectConfigCellsVisitor(context).visitNode(def);

        // sort List in streaming cells
        new CheckVisitorStep<Definition>(new CheckStreams(context), context).check(def);

        sw.printIntermediate("Parsing Configs");

        // ----------------------------------- parse rules
        Map<String, CachedSentence> cachedDef;
        // load definition if possible
        try {
            @SuppressWarnings("unchecked")
            Map<String, CachedSentence> cachedDefTemp = loader.load(Map.class, cache);
            cachedDef = cachedDefTemp;
        } catch (IOException | ClassNotFoundException e) {
            // it means the cache is not valid, or it doesn't exist
            cachedDef = new HashMap<>();
        }

        CacheLookupFilter clf = new CacheLookupFilter(context, cachedDef);
        int cachedSentences = 0;
        ParseRulesFilter prf = null;
        try {
            def = (Definition) clf.visitNode(def);
            cachedSentences = clf.getKept().size();
            prf = new ParseRulesFilter(context, clf.getKept(), kem);
            def = (Definition) prf.visitNode(def);
        } finally {
            // save definition
            loader.saveOrDie(cache, clf.getKept());
        }

        // really important to do disambiguation after we save the cache to disk because
        // the objects in the sentences are mutable, and we risk altering them and miss
        // warning and error messages when kompiling next time around
        def = (Definition) new DisambiguateRulesFilter(context, true, kem).visitNode(def);
        def = (Definition) new NormalizeASTTransformer(context, kem).visitNode(def);

        sw.printIntermediate("Parsing Rules [" + (clf.getKept().size() - cachedSentences) + "/" + clf.getKept().size() + "]");

        if (!context.kompileOptions.experimental.javaParserRules) {
            try {
                if (t2 != null) {
                    t2.join();
                    files.copyTempFileToKompiledFile("ground/Concrete.tbl", "Ground.tbl");
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                throw KExceptionManager.criticalError(
                        "Thread was interrupted trying to run SDF2Table");
            }
        }

        return def;
    }
}
