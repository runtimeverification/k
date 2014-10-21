// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backend;
import org.kframework.compile.checks.CheckListDecl;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.compile.checks.CheckSyntaxDecl;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Source;
import org.kframework.kil.Term;
import org.kframework.kil.loader.AddAutoIncludedModulesVisitor;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectModuleImportsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.RemoveUnusedModules;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.outer.Outer;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter;
import org.kframework.parser.concrete.disambiguate.NormalizeASTTransformer;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PreferDotsFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter2;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
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
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.google.inject.Inject;

public class DefinitionLoader {

    private final Stopwatch sw;
    private final BinaryLoader loader;
    private final KExceptionManager kem;
    private final OuterParser outer;
    private final boolean documentation;
    private final boolean autoinclude;
    private final FileUtil files;

    @Inject
    public DefinitionLoader(
            Stopwatch sw,
            BinaryLoader loader,
            KExceptionManager kem,
            OuterParser outer,
            @Backend.Documentation boolean documentation,
            @Backend.Autoinclude boolean autoinclude,
            FileUtil files) {
        this.sw = sw;
        this.loader = loader;
        this.kem = kem;
        this.outer = outer;
        this.documentation = documentation;
        this.autoinclude = autoinclude;
        this.files = files;
    }

    public Definition loadDefinition(File mainFile, String lang, Context context) {
        Definition javaDef;
        File canoFile = mainFile.getAbsoluteFile();

        String extension = FilenameUtils.getExtension(mainFile.getAbsolutePath());
        if ("bin".equals(extension)) {
            javaDef = loader.loadOrDie(Definition.class, canoFile);

            sw.printIntermediate("Load definition from binary");

            javaDef.preprocess(context);

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
        try {
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
            def.setModulesMap(outer.getModulesMap());
            def.setItems(outer.getModuleItems());

            if (!documentation) {
                if (!def.getModulesMap().containsKey(context.kompileOptions.syntaxModule())) {
                    String msg = "Could not find main syntax module used to generate a parser for programs (X-SYNTAX). Using: '" + mainModule + "' instead.";
                    kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.INNER_PARSER, msg));
                    def.setMainSyntaxModule(mainModule);
                } else {
                    def.setMainSyntaxModule(context.kompileOptions.syntaxModule());
                }

                if (!def.getModulesMap().containsKey(mainModule)) {
                    String msg = "Could not find main module '" + mainModule + "'. Use --main-module option to specify another.";
                    kem.registerCompilerError(msg);
                }
            }
            sw.printIntermediate("Outer Parsing");

            //This following line was commented out to make the latex backend
            //parse files importing from other files
            def = (Definition) new RemoveUnusedModules(context, autoinclude).visitNode(def);

            // HERE: add labels to sorts

            def.preprocess(context);

            sw.printIntermediate("Preprocess");

            new CheckVisitorStep<Definition>(new CheckSyntaxDecl(context), context).check(def);
            new CheckVisitorStep<Definition>(new CheckListDecl(context), context).check(def);
            new CheckVisitorStep<Definition>(new CheckSortTopUniqueness(context), context).check(def);

            sw.printIntermediate("Checks");

            // ------------------------------------- generate files
            ResourceExtractor.ExtractDefSDF(files.resolveTemp("def"));
            ResourceExtractor.ExtractGroundSDF(files.resolveTemp("ground"));

            ResourceExtractor.ExtractProgramSDF(files.resolveTemp("pgm"));
            // ------------------------------------- generate parser TBL
            // cache the TBL if the sdf file is the same
            if (!documentation) {
                String oldSdfPgm = "";
                if (files.resolveKompiled("Program.sdf").exists())
                    oldSdfPgm = files.loadFromKompiled("Program.sdf");

                StringBuilder newSdfPgmBuilder = ProgramSDF.getSdfForPrograms(def, context);

                String newSdfPgm = newSdfPgmBuilder.toString();
                files.saveToTemp("pgm/Program.sdf", newSdfPgm);

                sw.printIntermediate("File Gen Pgm");

                if (!oldSdfPgm.equals(newSdfPgm) || !files.resolveKompiled("Program.tbl").exists()) {
                    Sdf2Table.run_sdf2table(files.resolveTemp("pgm"), "Program");
                    files.copyTempFileToKompiledDirectory("pgm/Program.sdf");
                    files.copyTempFileToKompiledDirectory("pgm/Program.tbl");
                    sw.printIntermediate("Generate TBLPgm");
                }
            }

            if(autoinclude)
                new AddAutoIncludedModulesVisitor(context).visitNode(def);
            // new CheckModulesAndFilesImportsDecl(context).visitNode(def);
            new CollectModuleImportsVisitor(context).visitNode(def);

            // ------------------------------------- generate parser TBL
            // cache the TBL if the sdf file is the same
            String oldSdf = "";
            if (files.resolveKompiled("Integration.sdf").exists())
                oldSdf = files.loadFromKompiled("Integration.sdf");
            String newSdf = DefinitionSDF.getSdfForDefinition(def, context).toString();
            files.saveToTemp("def/Integration.sdf", newSdf);;
            files.saveToTemp("ground/Integration.sdf", Definition2SDF.getSdfForDefinition(def, context).toString());

            sw.printIntermediate("File Gen Def");

            File cache = files.resolveKompiled("defx-cache.bin");
            if (!oldSdf.equals(newSdf) || !files.resolveKompiled("Rule.tbl").exists()
                    || !files.resolveKompiled("Ground.tbl").exists()) {
                try {
                    // delete the file with the cached/partially parsed rules
                    if (cache.exists() && !cache.delete()) {
                        kem.registerCriticalError("Could not delete file " + cache);
                    }
                    // Sdf2Table.run_sdf2table(new File(context.dotk.getAbsoluteFile() + "/def"), "Concrete");
                    Thread t1 = Sdf2Table.run_sdf2table_parallel(files.resolveTemp("def"), "Concrete");
                    if (!documentation) {
                        Thread t2 = Sdf2Table.run_sdf2table_parallel(files.resolveTemp("ground"), "Concrete");
                        t2.join();
                        files.copyTempFileToKompiledFile("ground/Concrete.tbl", "Ground.tbl");
                    }
                    t1.join();
                    files.copyTempFileToKompiledDirectory("def/Integration.sdf");
                    files.copyTempFileToKompiledFile("def/Concrete.tbl", "Rule.tbl");
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    kem.registerCriticalError(
                            "Thread was interrupted trying to run SDF2Table");
                }


                sw.printIntermediate("Generate TBLDef");
            }

            org.kframework.parser.concrete.KParser.ImportTblRule(files.resolveKompiled("."));

            sw.printIntermediate("Importing Files");
            // ------------------------------------- parse configs
            JavaClassesFactory.startConstruction(context);
            def = (Definition) new ParseConfigsFilter(context).visitNode(def);
            JavaClassesFactory.endConstruction();
            new CollectConfigCellsVisitor(context).visitNode(def);

            // sort List in streaming cells
            new CheckVisitorStep<Definition>(new CheckStreams(context), context).check(def);

            sw.printIntermediate("Parsing Configs");

            // ----------------------------------- parse rules
            JavaClassesFactory.startConstruction(context);
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
                prf = new ParseRulesFilter(context, clf.getKept());
                def = (Definition) prf.visitNode(def);
            } catch (ParseFailedException te) {
                te.printStackTrace();
            } finally {
                // save definition
                loader.saveOrDie(cache, clf.getKept());
            }
            JavaClassesFactory.endConstruction();

            // really important to do disambiguation after we save the cache to disk because
            // the objects in the sentences are mutable, and we risk altering them and miss
            // warning and error messages when kompiling next time around
            try {
                def = (Definition) new DisambiguateRulesFilter(context, true).visitNode(def);
            } catch (ParseFailedException te) {
                te.printStackTrace();
            }
            def = (Definition) new NormalizeASTTransformer(context).visitNode(def);

            sw.printIntermediate("Parsing Rules [" + (clf.getKept().size() - cachedSentences) + "/" + clf.getKept().size() + "]");

            return def;
        } catch (ParseFailedException e) {
            throw new AssertionError("should not throw TransformerException", e);
        }
    }

    /**
     * Parses a string representing a file with modules in it. Returns the complete parse tree. Any bubble rule has been parsed and disambiguated.
     *
     * @param content
     *            - the input string.
     * @param source
     *            - only for error reporting purposes. Can be empty string.
     * @param context
     *            - the context for disambiguation purposes.
     * @return A lightweight Definition element which contain all the definition items found in the string.
     */
    public static Definition parseString(String content, Source source, Context context) throws ParseFailedException {
        List<DefinitionItem> di = Outer.parse(source, content, context);

        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        def.setItems(di);

        // ------------------------------------- import files in Stratego
        org.kframework.parser.concrete.KParser.ImportTblRule(context.files.resolveKompiled("."));

        // ------------------------------------- parse configs
        JavaClassesFactory.startConstruction(context);
        def = (Definition) new ParseConfigsFilter(context, false).visitNode(def);
        JavaClassesFactory.endConstruction();

        // ----------------------------------- parse rules
        JavaClassesFactory.startConstruction(context);
        def = (Definition) new ParseRulesFilter(context).visitNode(def);
        def = (Definition) new DisambiguateRulesFilter(context, false).visitNode(def);
        def = (Definition) new NormalizeASTTransformer(context).visitNode(def);

        JavaClassesFactory.endConstruction();

        return def;
    }

    public static Term parseCmdString(String content, Source source, Sort startSymbol, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }
        String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
        Document doc = XmlLoader.getXMLDoc(parsed);
        XmlLoader.addSource(doc.getFirstChild(), source);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        org.kframework.kil.ASTNode config = JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        // TODO: reject rewrites
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        //if (checkInclusion)
        //    config = new InclusionFilter(localModule, context).visitNode(config);
        config = new TypeSystemFilter2(startSymbol, context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        config = new CorrectRewritePriorityFilter(context).visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        config = new PriorityFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context).visitNode(config);
        try {
            config = new TypeSystemFilter(context).visitNode(config);
            config = new TypeInferenceSupremumFilter(context).visitNode(config);
        } catch (ParseFailedException e) {
            e.report();
        }
        // config = new AmbDuplicateFilter(context).visitNode(config);
        // config = new TypeSystemFilter(context).visitNode(config);
        // config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        // config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        config = new PreferAvoidFilter(context).visitNode(config);
        config = new NormalizeASTTransformer(context).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        config = new AmbFilter(context).visitNode(config);

        return (Term) config;
    }

    public static ASTNode parsePattern(String pattern, Source source, Sort startSymbol, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }

        String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
        Document doc = XmlLoader.getXMLDoc(parsed);

        XmlLoader.addSource(doc.getFirstChild(), source);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        // TODO: reject rewrites
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        //if (checkInclusion)
        //    config = new InclusionFilter(localModule, context).visitNode(config);
        config = new TypeSystemFilter2(startSymbol, context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        config = new CorrectRewritePriorityFilter(context).visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        config = new PriorityFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context).visitNode(config);
        try {
            config = new TypeSystemFilter(context).visitNode(config);
            config = new TypeInferenceSupremumFilter(context).visitNode(config);
        } catch (ParseFailedException e) {
            e.report();
        }
        // config = new AmbDuplicateFilter(context).visitNode(config);
        // config = new TypeSystemFilter(context).visitNode(config);
        // config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        // config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        config = new PreferAvoidFilter(context).visitNode(config);
        config = new NormalizeASTTransformer(context).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        config = new AmbFilter(context).visitNode(config);

        return config;
    }

    public static ASTNode parsePatternAmbiguous(String pattern, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }

        String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
        Document doc = XmlLoader.getXMLDoc(parsed);

        // XmlLoader.addFilename(doc.getFirstChild(), filename);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        // TODO: don't allow rewrites
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        // config = new CorrectRewritePriorityFilter().visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        // config = new InclusionFilter(localModule).visitNode(config);
        // config = new VariableTypeInferenceFilter().visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        config = new TypeSystemFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context).visitNode(config);
        // config = new PriorityFilter().visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        // config = new PreferAvoidFilter().visitNode(config);
        config = new NormalizeASTTransformer(context).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        // config = new AmbFilter().visitNode(config);
        return config;
    }
}
