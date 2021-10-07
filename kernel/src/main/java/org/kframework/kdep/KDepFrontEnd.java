// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kdep;

import com.google.inject.Provider;
import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.Module;
import org.apache.commons.collections15.ListUtils;
import org.kframework.attributes.Source;
import org.kframework.kompile.Kompile;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ParserUtils;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;
import org.kframework.utils.options.OuterParsingOptions;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Frontend for kdep tool.
 * <p>
 * kdep is designed to generate a Makefile that contains the dependencies
 * that kompile has on files when you run it. This can be used in order to ensure that if any
 * of the files required by a k definition are changed, the makefile will rerun kompile.
 * <p>
 * Example Makefile snippet:
 * <p>
 * <pre>
 *     .depend:
 *             kdep definition.k -d "directory" -I includes > .depend
 *
 *     include .depend
 * </pre>
 */
public class KDepFrontEnd extends FrontEnd {

    private final KDepOptions kdepOptions;
    private final OuterParsingOptions options;
    private final KExceptionManager kem;
    private final Stopwatch sw;
    private final Provider<FileUtil> files;
    private final GlobalOptions globalOptions;

    @Inject
    public KDepFrontEnd(
            KDepOptions kdepOptions,
            OuterParsingOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            @Usage String usage,
            Stopwatch sw,
            JarInfo jarInfo,
            Provider<FileUtil> files) {
        super(kem, globalOptions, usage, jarInfo, files);
        this.kdepOptions = kdepOptions;
        this.options = options;
        this.globalOptions = globalOptions;
        this.kem = kem;
        this.sw = sw;
        this.files = files;
    }

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new KDepModule());
        modules.add(new JCommanderModule());
        modules.add(new CommonModule());
        return modules;
    }

    @Override
    protected int run() {
        ParserUtils parser = new ParserUtils(files.get(), kem, globalOptions, options);
        List<org.kframework.kil.Module> modules = new ArrayList<>();
        Source source = Source.apply(options.mainDefinitionFile(files.get()).getAbsolutePath());
        File currentDirectory = options.mainDefinitionFile(files.get()).getParentFile();
        List<File> lookupDirectories = ListUtils.union(options.includes.stream()
                        .map(files.get()::resolveWorkingDirectory).collect(Collectors.toList()),
                Lists.newArrayList(Kompile.BUILTIN_DIRECTORY));

        Set<File> requiredFiles = new HashSet<>();
        // load builtin files if needed first
        if (!options.noPrelude) {
            modules.addAll(parser.slurp(Kompile.REQUIRE_PRELUDE_K,
                    source,
                    currentDirectory,
                    lookupDirectories,
                    requiredFiles));
        }

        modules.addAll(parser.slurp(FileUtil.load(options.mainDefinitionFile(files.get())),
                source,
                currentDirectory,
                lookupDirectories,
                requiredFiles));;
        Set<File> allFiles = modules.stream().map(m -> new File(m.getSource().source())).collect(Collectors.toSet());
        System.out.println(files.get().resolveWorkingDirectory(".").toURI().relativize(files.get().resolveKompiled("timestamp").toURI()).getPath() + " : \\");

        List<File> sortedFiles = new ArrayList<File>(allFiles);
        Collections.sort(sortedFiles, (File a, File b) -> {
          return a.getAbsolutePath().compareTo(b.getAbsolutePath());
        });

        for (File file : sortedFiles) {
            System.out.println("    " + file.getAbsolutePath() + " \\");
        }
        System.out.println();

        if (this.kdepOptions.alsoRemakeDepend) {
            System.out.println("DEPEND_FILE=$(lastword $(MAKEFILE_LIST))");
            System.out.println("$(DEPEND_FILE) : " + " \\");
            System.out.println("    $(wildcard \\");

            for (File file : sortedFiles) {
                System.out.println("        " + file.getAbsolutePath() + " \\");
            }

            System.out.println("    )");
        }
        return 0;
    }
}
