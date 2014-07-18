// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kast;

import java.io.*;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.backend.unparser.IndentationOptions;
import org.kframework.backend.unparser.KastFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Sort;
import org.kframework.kil.Source;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.main.FrontEnd;
import org.kframework.parser.ProgramLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.Main;
import com.beust.jcommander.ParameterException;
import com.google.inject.Inject;
import com.google.inject.Module;
import com.google.inject.Provider;

public class KastFrontEnd extends FrontEnd {

    public static Module[] getModules(String[] args) {
        try {
            KastOptions options = new KastOptions();

            return new Module[] {
                    new KastModule(options),
                    new JCommanderModule(args),
                    new CommonModule() };
        } catch (ParameterException ex) {
            printBootError(ex.getMessage());
            return null;
        }
    }

    private final KastOptions options;
    private final Provider<Context> contextProvider;
    private final Stopwatch sw;

    @Inject
    KastFrontEnd(
            KastOptions options,
            @Main Provider<Context> contextProvider,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Stopwatch sw,
            KExceptionManager kem,
            JarInfo jarInfo) {
        super(kem, options.global, usage, experimentalUsage, jarInfo);
        this.options = options;
        this.contextProvider = contextProvider;
        this.sw = sw;
    }

    /**
     *
     * @return true if the application terminated normally; false otherwise
     */
    @Override
    public boolean run() {
        String stringToParse = options.stringToParse();
        Source source = options.source();

        Context context = contextProvider.get();
        Sort sort = options.sort(context);

        try {
            ASTNode out = ProgramLoader.processPgm(stringToParse.getBytes(), source, sort, context, options.parser);
            StringBuilder kast;
            if (options.experimental.pretty) {
                IndentationOptions indentationOptions = new IndentationOptions(options.experimental.maxWidth(),
                        options.experimental.auxTabSize, options.experimental.tabSize);
                KastFilter kastFilter = new KastFilter(indentationOptions, options.experimental.nextLine, context);
                kastFilter.visitNode(out);
                kast = kastFilter.getResult();
            } else {
                MaudeFilter maudeFilter = new MaudeFilter(context);
                maudeFilter.visitNode(out);
                kast = maudeFilter.getResult();
                kast.append("\n");
            }

            try {
                Writer outWriter = new OutputStreamWriter(System.out);
                try {
                    FileUtil.toWriter(kast, outWriter);
                } finally {
                    outWriter.flush();
                }
            } catch (IOException e) {
                e.printStackTrace();
            }

            sw.printIntermediate("Maudify Program");
            sw.printTotal("Total");
            return true;
        } catch (ParseFailedException e) {
            e.report();
            return false;
        }
    }
}
