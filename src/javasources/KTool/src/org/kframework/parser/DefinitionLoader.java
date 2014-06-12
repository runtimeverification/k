// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser;

import java.io.File;
import java.io.IOException;
import java.util.List;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.kframework.compile.checks.CheckListDecl;
import org.kframework.compile.checks.CheckSortTopUniqueness;
import org.kframework.compile.checks.CheckStreams;
import org.kframework.compile.checks.CheckSyntaxDecl;
import org.kframework.compile.utils.CheckVisitorStep;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Term;
import org.kframework.kil.loader.AddAutoIncludedModulesVisitor;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectModuleImportsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.RemoveUnusedModules;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.basic.Basic;
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
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter2;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.parser.generator.BasicParser;
import org.kframework.parser.generator.Definition2SDF;
import org.kframework.parser.generator.DefinitionSDF;
import org.kframework.parser.generator.ParseConfigsFilter;
import org.kframework.parser.generator.ParseRulesFilter;
import org.kframework.parser.generator.ProgramSDF;
import org.kframework.parser.utils.ResourceExtractor;
import org.kframework.parser.utils.Sdf2Table;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class DefinitionLoader {
    public static Definition loadDefinition(File mainFile, String lang, boolean autoinclude, Context context) throws IOException {
        Definition javaDef;
        File canoFile = mainFile.getCanonicalFile();

        String extension = FilenameUtils.getExtension(mainFile.getAbsolutePath());
        if ("bin".equals(extension)) {
            javaDef = (Definition) BinaryLoader.load(canoFile.toString());

            Stopwatch.instance().printIntermediate("Load definition from binary");

            javaDef.preprocess(context);

            Stopwatch.instance().printIntermediate("Preprocess");

        } else {
            javaDef = parseDefinition(mainFile, lang, autoinclude, context);

            BinaryLoader.save(context.kompiled.getAbsolutePath() + "/defx-" + context.kompileOptions.backend.name().toLowerCase() + ".bin", javaDef);
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
    public static Definition parseDefinition(File mainFile, String mainModule, boolean autoinclude, Context context) {
        try {
            // for now just use this file as main argument
            // ------------------------------------- basic parsing

            BasicParser bparser = new BasicParser(autoinclude, context.kompileOptions);
            bparser.slurp(mainFile.getPath(), context);

            // transfer information from the BasicParser object, to the Definition object
            org.kframework.kil.Definition def = new org.kframework.kil.Definition();
            try {
                def.setMainFile(mainFile.getCanonicalPath());
            } catch (IOException e) {
                // this isn't worth crashing the application over, so just use the absolute path
                def.setMainFile(mainFile.getAbsolutePath());
            }
            def.setMainModule(mainModule);
            def.setModulesMap(bparser.getModulesMap());
            def.setItems(bparser.getModuleItems());

            if (!context.kompileOptions.backend.documentation()) {
                if (!def.getModulesMap().containsKey(context.kompileOptions.syntaxModule())) {
                    String msg = "Could not find main syntax module used to generate a parser for programs (X-SYNTAX). Using: '" + mainModule + "' instead.";
                    GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.INNER_PARSER, msg, def.getMainFile(), "File system."));
                    def.setMainSyntaxModule(mainModule);
                } else {
                    def.setMainSyntaxModule(context.kompileOptions.syntaxModule());
                }
                
                if (!def.getModulesMap().containsKey(mainModule)) {
                    String msg = "Could not find main module '" + mainModule + "'. Use --main-module option to specify another.";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.COMPILER, msg, def.getMainFile(), "File system."));
                }
            }
            Stopwatch.instance().printIntermediate("Basic Parsing");

            //This following line was commented out to make the latex backend 
            //parse files importing from other files
            def = (Definition) new RemoveUnusedModules(context, autoinclude).visitNode(def);
            
            // HERE: add labels to sorts

            def.preprocess(context);

            Stopwatch.instance().printIntermediate("Preprocess");

            new CheckVisitorStep<Definition>(new CheckSyntaxDecl(context), context).check(def);
            new CheckVisitorStep<Definition>(new CheckListDecl(context), context).check(def);
            new CheckVisitorStep<Definition>(new CheckSortTopUniqueness(context), context).check(def);

            Stopwatch.instance().printIntermediate("Checks");

            // ------------------------------------- generate files
            try {
                ResourceExtractor.ExtractDefSDF(new File(context.dotk, "def"));
                ResourceExtractor.ExtractGroundSDF(new File(context.dotk, "ground"));
    
                ResourceExtractor.ExtractProgramSDF(new File(context.dotk, "pgm"));
            } catch (IOException e) {
                if (context.globalOptions.debug) {
                    e.printStackTrace();
                }
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                        "IO error detected writing to " + context.kompiled.getAbsolutePath()));
            }
            // ------------------------------------- generate parser TBL
            // cache the TBL if the sdf file is the same
            if (!context.kompileOptions.backend.documentation()) {
                String oldSdfPgm = "";
                if (new File(context.kompiled, "Program.sdf").exists())
                    oldSdfPgm = FileUtil.getFileContent(context.kompiled.getAbsolutePath() + "/Program.sdf");

                StringBuilder newSdfPgmBuilder = ProgramSDF.getSdfForPrograms(def, context);

                FileUtil.save(context.dotk.getAbsolutePath() + "/pgm/Program.sdf", newSdfPgmBuilder);
                String newSdfPgm = FileUtil.getFileContent(context.dotk.getAbsolutePath() + "/pgm/Program.sdf");

                Stopwatch.instance().printIntermediate("File Gen Pgm");

                if (!oldSdfPgm.equals(newSdfPgm) || !new File(context.kompiled, "Program.tbl").exists()) {
                    Sdf2Table.run_sdf2table(new File(context.dotk.getAbsoluteFile() + "/pgm"), "Program");
                    try {
                        FileUtils.copyFileToDirectory(new File(context.dotk, "pgm/Program.sdf"), context.kompiled);
                        FileUtils.copyFileToDirectory(new File(context.dotk, "pgm/Program.tbl"), context.kompiled);
                        } catch (IOException e) {
                        if (context.globalOptions.debug) {
                            e.printStackTrace();
                        }
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                                "IO error detected writing program parser to file"));
                        return null; //unreachable
                    }
                    
                    Stopwatch.instance().printIntermediate("Generate TBLPgm");
                }
            }

            new AddAutoIncludedModulesVisitor(context).visitNode(def);
            // new CheckModulesAndFilesImportsDecl(context).visitNode(def);
            new CollectModuleImportsVisitor(context).visitNode(def);

            // ------------------------------------- generate parser TBL
            // cache the TBL if the sdf file is the same
            String oldSdf = "";
            if (new File(context.kompiled, "Integration.sdf").exists())
                oldSdf = FileUtil.getFileContent(context.kompiled.getAbsolutePath() + "/Integration.sdf");
            FileUtil.save(context.dotk.getAbsolutePath() + "/def/Integration.sdf", DefinitionSDF.getSdfForDefinition(def, context));
            FileUtil.save(context.dotk.getAbsolutePath() + "/ground/Integration.sdf", Definition2SDF.getSdfForDefinition(def, context));
            String newSdf = FileUtil.getFileContent(context.dotk.getAbsolutePath() + "/def/Integration.sdf");

            Stopwatch.instance().printIntermediate("File Gen Def");

            if (!oldSdf.equals(newSdf) || !new File(context.kompiled, "Rule.tbl").exists()
                    || !new File(context.kompiled, "Ground.tbl").exists()) {
                try {
                    // Sdf2Table.run_sdf2table(new File(context.dotk.getAbsoluteFile() + "/def"), "Concrete");
                    Thread t1 = Sdf2Table.run_sdf2table_parallel(new File(context.dotk.getAbsoluteFile() + "/def"), "Concrete");
                    if (!context.kompileOptions.backend.documentation()) {
                        Thread t2 = Sdf2Table.run_sdf2table_parallel(new File(context.dotk.getAbsoluteFile() + "/ground"), "Concrete");
                        t2.join();
                        try {
                            FileUtils.copyFile(new File(context.dotk, "ground/Concrete.tbl"), new File(context.kompiled, "Ground.tbl"));
                        } catch (IOException e) {
                            if (context.globalOptions.debug) {
                                e.printStackTrace();
                            }
                            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                                    "IO error detected writing ground parser to file"));
                            return null; //unreachable
                        }
                    }
                    t1.join();
                    try {
                        FileUtils.copyFileToDirectory(new File(context.dotk, "def/Integration.sdf"), context.kompiled);
                        FileUtils.copyFile(new File(context.dotk, "def/Concrete.tbl"), new File(context.kompiled, "Rule.tbl"));
                    } catch (IOException e) {
                        if (context.globalOptions.debug) {
                            e.printStackTrace();
                        }
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, 
                                "IO error detected writing rule parser to file"));
                        return null; //unreachable
                    }
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, 
                            "Thread was interrupted trying to run SDF2Table"));
                }
                
                
                Stopwatch.instance().printIntermediate("Generate TBLDef");
            }
            
            org.kframework.parser.concrete.KParser.ImportTblRule(context.kompiled);

            Stopwatch.instance().printIntermediate("Importing Files");
            // ------------------------------------- parse configs
            JavaClassesFactory.startConstruction(context);
            def = (Definition) new ParseConfigsFilter(context).visitNode(def);
            JavaClassesFactory.endConstruction();
            new CollectConfigCellsVisitor(context).visitNode(def);

            // sort List in streaming cells
            new CheckVisitorStep<Definition>(new CheckStreams(context), context).check(def);

            Stopwatch.instance().printIntermediate("Parsing Configs");

            // ----------------------------------- parse rules
            JavaClassesFactory.startConstruction(context);
            def = (Definition) new ParseRulesFilter(context).visitNode(def);
            JavaClassesFactory.endConstruction();
            def = (Definition) new NormalizeASTTransformer(context).visitNode(def);


            Stopwatch.instance().printIntermediate("Parsing Rules");

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
     * @param filename
     *            - only for error reporting purposes. Can be empty string.
     * @param context
     *            - the context for disambiguation purposes.
     * @return A lightweight Definition element which contain all the definition items found in the string.
     */
    public static Definition parseString(String content, String filename, Context context) throws ParseFailedException {
        List<DefinitionItem> di = Basic.parse(filename, content, context);

        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        def.setItems(di);

        // ------------------------------------- import files in Stratego
        org.kframework.parser.concrete.KParser.ImportTblRule(context.kompiled);

        // ------------------------------------- parse configs
        JavaClassesFactory.startConstruction(context);
        def = (Definition) new ParseConfigsFilter(context, false).visitNode(def);
        JavaClassesFactory.endConstruction();

        // ----------------------------------- parse rules
        JavaClassesFactory.startConstruction(context);
        def = (Definition) new ParseRulesFilter(context, false).visitNode(def);
        def = (Definition) new NormalizeASTTransformer(context).visitNode(def);

        JavaClassesFactory.endConstruction();

        return def;
    }

    public static Term parseCmdString(String content, String filename, String startSymbol, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }
        String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
        Document doc = XmlLoader.getXMLDoc(parsed);
        XmlLoader.addFilename(doc.getFirstChild(), filename);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        org.kframework.kil.ASTNode config = (Term) JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());
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

    public static ASTNode parsePattern(String pattern, String filename, String startSymbol, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }

        String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
        Document doc = XmlLoader.getXMLDoc(parsed);

        XmlLoader.addFilename(doc.getFirstChild(), filename);
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
