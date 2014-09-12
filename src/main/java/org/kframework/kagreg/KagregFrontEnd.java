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
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Context;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.parser.DefinitionLoader;
import org.kframework.parser.concrete.KParser;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.FirstArg;
import org.kframework.utils.inject.SecondArg;
import org.kframework.utils.inject.CommonModule;

import com.google.inject.AbstractModule;
import com.google.inject.Inject;
import com.google.inject.Module;

/*
 * @author StefanC
 *
 * Front-end for the equivalance checker.
 */
public class KagregFrontEnd extends FrontEnd {

    private final String firstDefinitionFileName, secondDefinitionFileName;
    private final GlobalOptions globalOptions;
    private final DefinitionLoader loader;
    private final KExceptionManager kem;

    @Inject
    KagregFrontEnd(KExceptionManager kem,
            @FirstArg String firstDefinitionFileName,
            @SecondArg String secondDefinitionFileName,
            GlobalOptions globalOptions,
            DefinitionLoader loader,
            JarInfo jarInfo) {
        super(kem, globalOptions, "Usage: kagreg <file1.k> <file2.k>", "", jarInfo);
        this.firstDefinitionFileName = firstDefinitionFileName;
        this.secondDefinitionFileName = secondDefinitionFileName;
        this.globalOptions = globalOptions;
        this.loader = loader;
        this.kem = kem;
    }

    public static Module[] getModules(final String[] args) {
        if (args.length != 2) {
            printBootError("There must be exactly two K definitions as arguments to kagreg.");
            return null;
        }

        final GlobalOptions globalOptions = new GlobalOptions();
        globalOptions.verbose = true;

        return new Module[] { new CommonModule(), new AbstractModule() {
            @Override
            protected void configure() {
                bind(FrontEnd.class).to(KagregFrontEnd.class);
                bind(Tool.class).toInstance(Tool.OTHER);
                bind(String.class).annotatedWith(FirstArg.class).toInstance(args[0]);
                bind(String.class).annotatedWith(SecondArg.class).toInstance(args[1]);
                bind(GlobalOptions.class).toInstance(globalOptions);
            }
        }};
    }

    @Override
    public boolean run() {

        File firstDefinitionFile = new File(firstDefinitionFileName);
        File secondDefinitionFile = new File(secondDefinitionFileName);

        if (!firstDefinitionFile.exists()) {
            File errorFile = firstDefinitionFile;
            firstDefinitionFile = new File(firstDefinitionFileName + ".k");
            if (!firstDefinitionFile.exists()) {
                String msg = "File: " + errorFile.getName() + "(.k) not found.";
                kem.registerCriticalError(msg);
            }
        }
        if (!secondDefinitionFile.exists()) {
            File errorFile = secondDefinitionFile;
            secondDefinitionFile = new File(secondDefinitionFileName + ".k");
            if (!secondDefinitionFile.exists()) {
                String msg = "File: " + errorFile.getName() + "(.k) not found.";
                kem.registerCriticalError(msg);
            }
        }

//        GlobalSettings.symbolicEquality = false;
//        GlobalSettings.SMT = false;
//        GlobalSettings.javaBackend = false;
//        GlobalSettings.NOSMT = true;

        String firstLang = FileUtil.getMainModule(firstDefinitionFile.getName());
        String secondLang = FileUtil.getMainModule(secondDefinitionFile.getName());

        Context context1 = new Context();
        context1.globalOptions = globalOptions;
        context1.dotk = new File(firstDefinitionFile.getAbsoluteFile().getParent() + File.separator + ".k");
        context1.dotk.mkdirs();
        Definition firstDef = loader.loadDefinition(firstDefinitionFile, firstLang,
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
        Context context2 = new Context();
        context2.globalOptions = globalOptions;
        assert context2 != null;
        context2.dotk = new File(secondDefinitionFile.getAbsoluteFile().getParent() + File.separator + ".k");
        context2.dotk.mkdirs();
        Definition secondDef = loader.loadDefinition(secondDefinitionFile, secondLang,
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
            return false;
        } catch (ConfigurationNotFound e) {
            System.err.println("The first definition must have a configuration; found none.");
            return false;
        }

        Configuration secondConf = null;
        try {
            secondConf = secondDef.getSingletonConfiguration();
        } catch (ConfigurationNotUnique e) {
            System.err.println("Expecting a unique configuration in the second definition; found several.");
            return false;
        } catch (ConfigurationNotFound e) {
            System.err.println("The second definition must have a configuration; found none.");
            return false;
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

        List<Sort> labeledSorts = new ArrayList<>();
        labeledSorts.add(Sort.KRESULT); // temporary bug fix for https://code.google.com/p/k-framework/issues/detail?id=541
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
        } catch (IOException e) {
            kem.registerCriticalError("Could not write to result.k", e);
        }
        return true;
    }
}
