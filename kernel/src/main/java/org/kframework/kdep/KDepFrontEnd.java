// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kdep;

import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.Module;
import org.apache.commons.collections15.ListUtils;
import org.kframework.kompile.Kompile;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.CommonModule;
import org.kframework.utils.inject.JCommanderModule;
import org.kframework.utils.inject.JCommanderModule.ExperimentalUsage;
import org.kframework.utils.inject.JCommanderModule.Usage;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Frontend for kdep tool.
 *
 * kdep is designed to generate a Makefile that contains the dependencies
 * that kompile has on files when you run it. This can be used in order to ensure that if any
 * of the files required by a k definition are changed, the makefile will rerun kompile.
 *
 * Example Makefile snippet:
 *
 * <pre>
 *     .depend:
 *             kdep definition.k -d "directory" -I includes > .depend
 *
 *     include .depend
 * </pre>
 */
public class KDepFrontEnd extends FrontEnd {

    private final KDepOptions options;
    private final KExceptionManager kem;
    private final Stopwatch sw;
    private final FileUtil files;
    private final ParserUtils parser;

    @Inject
    public KDepFrontEnd(
            KDepOptions options,
            KExceptionManager kem,
            GlobalOptions globalOptions,
            @Usage String usage,
            @ExperimentalUsage String experimentalUsage,
            Stopwatch sw,
            JarInfo jarInfo,
            FileUtil files) {
        super(kem, globalOptions, usage, experimentalUsage, jarInfo, files);
        this.options = options;
        this.kem = kem;
        this.sw = sw;
        this.files = files;
        this.parser = new ParserUtils(files, kem, options.global);
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
        String prelude = Kompile.REQUIRE_PRELUDE_K;
        if (options.noPrelude) {
            prelude = "";
        }

        List<org.kframework.kil.Module> modules = parser.slurp(prelude + FileUtil.load(options.mainDefinitionFile()),
                options.mainDefinitionFile(),
                options.mainDefinitionFile().getParentFile(),
                ListUtils.union(options.includes.stream()
                        .map(files::resolveWorkingDirectory).collect(Collectors.toList()),
                Lists.newArrayList(Kompile.BUILTIN_DIRECTORY)));
        Set<File> allFiles = modules.stream().map(m -> new File(m.getSource().source())).collect(Collectors.toSet());
        System.out.println(files.resolveWorkingDirectory(".").toURI().relativize(files.resolveKompiled("timestamp").toURI()).getPath() + " : \\");
        for (File file : allFiles) {
            System.out.println("    " + file.getAbsolutePath() + " \\");
        }
        System.out.println();
        return 0;
    }
}
