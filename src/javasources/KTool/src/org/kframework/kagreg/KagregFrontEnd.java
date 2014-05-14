// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kagreg;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.unparser.Indenter;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.compile.transformers.AddKCell;
import org.kframework.kil.Configuration;
import org.kframework.kil.ConfigurationNotFound;
import org.kframework.kil.ConfigurationNotUnique;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.loader.Context;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.DefinitionLoader;
import org.kframework.parser.concrete.KParser;
import org.kframework.utils.Error;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

/*
 * @author StefanC
 * 
 * Front-end for the equivalance checker.
 */
public class KagregFrontEnd {

    public static void kagreg(String[] args) throws IOException {
        if (args.length != 2) {
            Error.report("There must be exactly two K definitions as arguments to kagreg.");
        }
        String firstDefinitionFileName = args[0];
        String secondDefinitionFileName = args[1];

        File firstDefinitionFile = new File(firstDefinitionFileName);
        File secondDefinitionFile = new File(secondDefinitionFileName);

        if (!firstDefinitionFile.exists()) {
            File errorFile = firstDefinitionFile;
            firstDefinitionFile = new File(firstDefinitionFileName + ".k");
            if (!firstDefinitionFile.exists()) {
                String msg = "File: " + errorFile.getName() + "(.k) not found.";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, errorFile.getAbsolutePath(), "File system."));
            }
        }
        if (!secondDefinitionFile.exists()) {
            File errorFile = secondDefinitionFile;
            secondDefinitionFile = new File(secondDefinitionFileName + ".k");
            if (!secondDefinitionFile.exists()) {
                String msg = "File: " + errorFile.getName() + "(.k) not found.";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, errorFile.getAbsolutePath(), "File system."));
            }
        }
        
        GlobalOptions globalOptions = new GlobalOptions();
        globalOptions.verbose = true;
        globalOptions.initialize();
        
//        GlobalSettings.symbolicEquality = false;
//        GlobalSettings.SMT = false;
//        GlobalSettings.javaBackend = false;
//        GlobalSettings.NOSMT = true;

        String firstLang = FileUtil.getMainModule(firstDefinitionFile.getName());
        String secondLang = FileUtil.getMainModule(secondDefinitionFile.getName());
        
        Context context1 = new Context(globalOptions);
        context1.dotk = new File(firstDefinitionFile.getCanonicalFile().getParent() + File.separator + ".k");
        context1.dotk.mkdirs();
        Definition firstDef = DefinitionLoader.loadDefinition(firstDefinitionFile, firstLang, true,
                context1);
        firstDef = (Definition) new AddKCell(context1).visitNode(firstDef);
        firstDef = (Definition) new RenameCellsTransformer(new AppendRenameStrategy("1"), context1).visitNode(firstDef);
        firstDef = (Definition) new RenameVariablesTransformer(new AppendRenameStrategy("1"), context1).visitNode(firstDef);
        CollectImportsVisitor collectImportsVisitor1 = new CollectImportsVisitor(context1, false);
        collectImportsVisitor1.visitNode(firstDef);
        List<Import> imports1 = collectImportsVisitor1.getImports();
        
//        GlobalSettings.symbolicEquality = false;
//        GlobalSettings.SMT = false;
//        GlobalSettings.javaBackend = false;
//        GlobalSettings.NOSMT = true;

        KParser.reset();
        Context context2 = new Context(globalOptions);
        assert context2 != null;
        context2.dotk = new File(secondDefinitionFile.getCanonicalFile().getParent() + File.separator + ".k");
        context2.dotk.mkdirs();
        Definition secondDef = DefinitionLoader.loadDefinition(secondDefinitionFile, secondLang, true,
                context2);
        secondDef = (Definition) new AddKCell(context2).visitNode(secondDef);
        secondDef = (Definition) new RenameCellsTransformer(new AppendRenameStrategy("2"), context2).visitNode(secondDef);
        secondDef = (Definition) new RenameVariablesTransformer(new AppendRenameStrategy("2"), context2).visitNode(secondDef);
        CollectImportsVisitor collectImportsVisitor2 = new CollectImportsVisitor(context2, false);
        collectImportsVisitor2.visitNode(secondDef);
        List<Import> imports2 = collectImportsVisitor2.getImports();

        Configuration firstConf = null;
        try {
            firstConf = firstDef.getSingletonConfiguration();
        } catch (ConfigurationNotUnique e) {
            System.err.println("Expecting a unique configuration in the first definition; found several.");
            return;
        } catch (ConfigurationNotFound e) {
            System.err.println("The first definition must have a configuration; found none.");
            return;
        }
        
        Configuration secondConf = null;
        try {
            secondConf = secondDef.getSingletonConfiguration();
        } catch (ConfigurationNotUnique e) {
            System.err.println("Expecting a unique configuration in the second definition; found several.");
            return;
        } catch (ConfigurationNotFound e) {
            System.err.println("The second definition must have a configuration; found none.");
            return;
        }

        Indenter indenter = new Indenter();
        
        indenter.write("module RESULT");
        indenter.endLine();
        indenter.indent(UnparserFilter.TAB);
        List<Import> allImports = new ArrayList<Import>();
        allImports.addAll(imports1);
        allImports.addAll(imports2);
        for (Import i : allImports) {
            if (i.getName().endsWith("-SYNTAX") || i.getName().startsWith("AUTO-INCLUDED")) {
                continue;
            }
            indenter.write("imports " + i.getName());
            indenter.endLine();
        }
        indenter.endLine();

        List<String> labeledSorts = new ArrayList<String>();
        labeledSorts.add("KResult"); // temporary bug fix for https://code.google.com/p/k-framework/issues/detail?id=541
        AddSortLabels addSortLabels1 = new AddSortLabels(context1, labeledSorts);
        firstDef = (Definition) addSortLabels1.visitNode(firstDef);

        AddSortLabels addSortLabels2 = new AddSortLabels(context2, labeledSorts);
        secondDef = (Definition) addSortLabels2.visitNode(secondDef);

        UnparserFilter unparserFirst = new UnparserFilter(context1);
        unparserFirst.setIndenter(indenter);
        unparserFirst.setForEquivalence();
        unparserFirst.visitNode(firstDef);
        
        UnparserFilter unparserSecond = new UnparserFilter(context2);
        unparserSecond.setIndenter(indenter);
        unparserSecond.setForEquivalence();
        unparserSecond.visitNode(secondDef);
        
        indenter.write("configuration");
        indenter.endLine();
        indenter.indent(UnparserFilter.TAB);

        indenter.write("<aggregation>");
        indenter.endLine();
        indenter.indent(UnparserFilter.TAB);

        indenter.indent(UnparserFilter.TAB);
        indenter.write("<first>");
        indenter.endLine();
        indenter.indent(UnparserFilter.TAB);
        UnparserFilter unparserFirstConfiguration = new UnparserFilter(context1);
        unparserFirstConfiguration.setIndenter(indenter);
        unparserFirstConfiguration.setInConfiguration(true);
        unparserFirstConfiguration.visitNode(firstConf.getBody());
        indenter.endLine();
        indenter.unindent();
        indenter.write("</first>");
        indenter.endLine();
        indenter.unindent();

        indenter.write("<second>");
        indenter.endLine();
        indenter.indent(UnparserFilter.TAB);
        UnparserFilter unparserSecondConfiguration = new UnparserFilter(context2);
        unparserSecondConfiguration.setIndenter(indenter);
        unparserSecondConfiguration.setInConfiguration(true);
        unparserSecondConfiguration.visitNode(secondConf.getBody());
        indenter.endLine();
        indenter.unindent();
        indenter.write("</second>");
        indenter.endLine();
        indenter.unindent();
        
        indenter.write("</aggregation>");
        indenter.endLine();
        indenter.unindent();

        indenter.unindent(); // "configuration"
        indenter.endLine();
        indenter.write("endmodule");
        indenter.endLine();

        try (Writer writer = new BufferedWriter(new FileWriter("result.k"))) {
            writer.write(indenter.toString());
        }
    }
}
