// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.backend.haskell;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.compile.AddSortInjections;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.RunProcess;
import org.kframework.main.Main;
import org.kframework.rewriter.Rewriter;
import org.kframework.rewriter.SearchType;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import scala.Tuple2;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;


@RequestScoped
public class HaskellRewriter implements Function<Module, Rewriter> {

    private final FileUtil files;
    private final CompiledDefinition def;
    private final KRunOptions options;
    private final HaskellKRunOptions haskellKRunOptions;

    @Inject
    public HaskellRewriter(
            FileUtil files,
            CompiledDefinition def,
            KRunOptions options,
            HaskellKRunOptions haskellKRunOptions
            ) {
        this.files = files;
        this.def = def;
        this.haskellKRunOptions = haskellKRunOptions;
        this.options = options;
    }

    @Override
    public Rewriter apply(Module module) {
        if (!module.equals(def.executionModule())) {
            throw KEMException.criticalError("Invalid module specified for rewriting. Haskell backend only supports rewriting over" +
                    " the definition's main module.");
        }
        return new Rewriter() {
            @Override
            public RewriterResult execute(K k, Optional<Integer> depth) {
                Module mod = def.executionModule();
                ModuleToKORE converter = new ModuleToKORE(mod, files, def.topCellInitializer);
                K kWithInjections = new AddSortInjections(mod).addInjections(k);
                converter.convert(kWithInjections);
                String koreOutput = converter.toString();
                String defPath = files.resolveKompiled("definition.kore").getAbsolutePath();
                String moduleName = mod.name();
                if (haskellKRunOptions.dryRun) {
                    String pgmName = options.configurationCreation.pgm()+".kore";
                    files.saveToWorkingDirectory(pgmName, koreOutput);

                    String pgmPath = files.resolveWorkingDirectory(pgmName).getPath();
                    System.out.println(haskellKRunOptions.haskellBackendCommand
                                    + " " + defPath
                                    + " --module " + moduleName
                                    + " --pattern " + pgmPath);
                    options.print.output = OutputModes.NONE;
                } else {
                    files.saveToTemp("pgm.kore", koreOutput);
                    String pgmPath = files.resolveTemp("pgm.kore").getAbsolutePath();
                    String[] koreCommand = haskellKRunOptions.haskellBackendCommand.split("\\s+");
                    String koreDirectory = haskellKRunOptions.haskellBackendHome;
                    List<String> args = new ArrayList<String>();
                    args.addAll(Arrays.asList(koreCommand));
                    args.addAll(Arrays.asList(
                            defPath,
                            "--module", moduleName,
                            "--pattern", pgmPath));
                    if (options.depth != null) {
                        args.add("--depth");
                        args.add(options.depth.toString());
                    }
                    koreCommand = args.toArray(koreCommand);
                    try {
                        File korePath = koreDirectory == null ? null : new File(koreDirectory);
                        executeCommandBasic(korePath, koreCommand);
                    } catch (IOException e) {
                        e.printStackTrace();
                    } catch (InterruptedException e) {
                        e.printStackTrace();
                    }

                }
                return new RewriterResult(Optional.empty(), k);
            }

            @Override
            public K match(K k, Rule rule) {
                throw new UnsupportedOperationException();
            }

            @Override
            public Tuple2<RewriterResult, K> executeAndMatch(K k, Optional<Integer> depth, Rule rule) {
                throw new UnsupportedOperationException();
            }

            @Override
            public K search(K initialConfiguration, Optional<Integer> depth, Optional<Integer> bound, Rule pattern, SearchType searchType) {
                throw new UnsupportedOperationException();
            }

            @Override
            public K prove(Module rules) {
                throw new UnsupportedOperationException();
            }

            @Override
            public boolean equivalence(Rewriter firstDef, Rewriter secondDef, Module firstSpec, Module secondSpec) {
                throw new UnsupportedOperationException();
            }
        };
    }


    /**
     * Runs a command in the given directory,
     * @param workingDir directory to run in
     * @param command  commandline to run
     * @return
     * @throws IOException
     * @throws InterruptedException
     */
    private int executeCommandBasic(File workingDir, String... command) throws IOException, InterruptedException {
        int exit;
        ProcessBuilder pb = files.getProcessBuilder()
                .command(command);
        if (workingDir != null) {
            pb.directory(workingDir);
        }
        if (Main.isNailgun()) {

            Process p2 = pb.start();

            Thread in = new Thread(() -> {
                int count;
                byte[] buffer = new byte[8192];
                try {
                    while (true) {
                        count = System.in.read(buffer);
                        if (count < 0)
                            break;
                        p2.getOutputStream().write(buffer, 0, count);
                        p2.getOutputStream().flush();
                    }
                } catch (IOException e) {}
            });
            Thread out = RunProcess.getOutputStreamThread(p2::getInputStream, System.out);
            Thread err = RunProcess.getOutputStreamThread(p2::getErrorStream, System.err);
            in.start();
            out.start();
            err.start();

            exit = p2.waitFor();
            in.interrupt();
            in.join();
            out.join();
            err.join();
            System.out.flush();
            System.err.flush();
            return exit;
        } else {
            // if we're not nailgun, we can't do the above because System.in won't be interruptible,
            // and we don't really want or need to anyway.
            return pb.inheritIO().start().waitFor();
        }
    }

}

