// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.haskell;

import com.google.inject.Inject;
import org.kframework.RewriterResult;
import org.kframework.attributes.Att;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.ExpandMacros;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kprove.KProveOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.RunProcess;
import org.kframework.main.Main;
import org.kframework.parser.kore.Pattern;
import org.kframework.parser.kore.parser.KoreToK;
import org.kframework.parser.kore.parser.ParseError;
import org.kframework.parser.kore.parser.TextToKore;
import org.kframework.rewriter.Rewriter;
import org.kframework.rewriter.SearchType;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.StringUtil;
import scala.Tuple2;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.Properties;
import java.util.function.Function;

import static org.kframework.builtin.BooleanUtils.*;


@RequestScoped
public class HaskellRewriter implements Function<Definition, Rewriter> {

    private final FileUtil files;
    private final CompiledDefinition def;
    private final KRunOptions options;
    private final KompileOptions kompileOptions;
    private final KExceptionManager kem;
    private final HaskellKRunOptions haskellKRunOptions;
    private final KProveOptions kProveOptions;
    private final Properties idsToLabels;

    @Inject
    public HaskellRewriter(
            FileUtil files,
            CompiledDefinition def,
            KRunOptions kRunOptions,
            KompileOptions kompileOptions,
            KProveOptions kProveOptions,
            InitializeDefinition init,
            KExceptionManager kem,
            HaskellKRunOptions haskellKRunOptions
            ) {
        this.files = files;
        this.def = def;
        this.kem = kem;
        this.haskellKRunOptions = haskellKRunOptions;
        this.options = kRunOptions;
        this.kompileOptions = kompileOptions;
        this.kProveOptions = kProveOptions;
        this.idsToLabels = init.serialized;

    }

    @Override
    public Rewriter apply(Definition definition) {
        Module module = definition.mainModule();
        if (!module.equals(def.executionModule()) && kProveOptions.specModule != null) {
            throw KEMException.criticalError("Invalid module specified for rewriting. Haskell backend only supports rewriting over" +
                    " the definition's main module.");
        }
        return new Rewriter() {
            @Override
            public RewriterResult execute(K k, Optional<Integer> depth) {
                Module mod = def.executionModule();
                ModuleToKORE converter = new ModuleToKORE(mod, files, def.topCellInitializer);
                String koreOutput = getKoreString(k, mod, converter);
                String defPath = files.resolveKompiled("definition.kore").getAbsolutePath();
                String moduleName = mod.name();

                files.saveToTemp("pgm.kore", koreOutput);
                String pgmPath = files.resolveTemp("pgm.kore").getAbsolutePath();
                String[] koreCommand = haskellKRunOptions.haskellBackendCommand.split("\\s+");
                String koreDirectory = haskellKRunOptions.haskellBackendHome;
                File koreOutputFile = files.resolveTemp("result.kore");
                List<String> args = new ArrayList<String>();
                args.addAll(Arrays.asList(koreCommand));
                args.addAll(Arrays.asList(
                        defPath,
                        "--module", moduleName,
                        "--pattern", pgmPath,
                        "--output", koreOutputFile.getAbsolutePath()));
                if (options.depth != null) {
                    args.add("--depth");
                    args.add(options.depth.toString());
                }
                if (options.experimental.smt.smtPrelude != null) {
                    args.add("--smt-prelude");
                    args.add(options.experimental.smt.smtPrelude);
                }
                koreCommand = args.toArray(koreCommand);
                if (haskellKRunOptions.dryRun) {
                    System.out.println(String.join(" ", koreCommand));
                    options.print.output = OutputModes.NONE;
                } else {
                    try {
                        File korePath = koreDirectory == null ? null : new File(koreDirectory);
                        if (executeCommandBasic(korePath, koreCommand) != 0) {
                            throw KEMException.criticalError("Haskell backend returned non-zero exit code");
                        }
                        TextToKore textToKore = new TextToKore();
                        Pattern kore = textToKore.parsePattern(koreOutputFile);
                        KoreToK koreToK = new KoreToK(idsToLabels, mod.sortAttributesFor(), StringUtil::enquoteKString);
                        K outputK = koreToK.apply(kore);
                        return new RewriterResult(Optional.empty(), Optional.empty(), outputK);
                    } catch (IOException e) {
                        throw KEMException.criticalError("I/O Error while executing", e);
                    } catch (InterruptedException e) {
                        throw KEMException.criticalError("Interrupted while executing", e);
                    } catch (ParseError parseError) {
                        throw KEMException.criticalError("Error parsing haskell backend output", parseError);
                    }
                }

                return new RewriterResult(Optional.empty(), Optional.empty(), k);
            }

            @Override
            public K match(K k, Rule rule) {
                return search(k, Optional.of(0), Optional.empty(), rule, SearchType.STAR);
            }

            @Override
            public Tuple2<RewriterResult, K> executeAndMatch(K k, Optional<Integer> depth, Rule rule) {
                RewriterResult res = execute(k, depth);
                return Tuple2.apply(res, match(res.k(), rule));
            }

            @Override
            public K search(K initialConfiguration, Optional<Integer> depth, Optional<Integer> bound, Rule pattern, SearchType searchType) {
                Module mod = def.executionModule();
                String koreOutput = getKoreString(initialConfiguration, mod, new ModuleToKORE(mod, files, def.topCellInitializer));
                Sort initializerSort = mod.productionsFor().get(def.topCellInitializer).get().head().sort();
                K patternTerm = RewriteToTop.toLeft(pattern.body());
                if (patternTerm instanceof  KVariable) {
                    patternTerm = KORE.KVariable(((KVariable) patternTerm).name(), Att.empty().add(Sort.class, initializerSort));
                }
                K patternCondition = pattern.requires();
                String patternTermKore = getKoreString(patternTerm, mod, new ModuleToKORE(mod, files, def.topCellInitializer));
                String patternConditionKore;
                if (patternCondition.equals(TRUE)) {
                    patternConditionKore = "\\top{Sort" + initializerSort.name() + "{}}()";
                } else {
                    patternConditionKore =
                            "\\equals{SortBool{},Sort" + initializerSort.name() + "{}}("
                            + getKoreString(patternCondition, mod, new ModuleToKORE(mod, files, def.topCellInitializer))
                            + ", \\dv{SortBool{}}(\"true\")"
                            + ")";
                }
                String korePatternOutput = "\\and{Sort" + initializerSort.name() + "{}}("
                        + patternTermKore
                        + ", " + patternConditionKore
                        + ")";
                String defPath = files.resolveKompiled("definition.kore").getAbsolutePath();
                String moduleName = mod.name();

                files.saveToTemp("pgm.kore", koreOutput);
                String pgmPath = files.resolveTemp("pgm.kore").getAbsolutePath();
                files.saveToTemp("pattern.kore", korePatternOutput);
                String patternPath = files.resolveTemp("pattern.kore").getAbsolutePath();
                String[] koreCommand = haskellKRunOptions.haskellBackendCommand.split("\\s+");
                String koreDirectory = haskellKRunOptions.haskellBackendHome;
                File koreOutputFile = files.resolveTemp("result.kore");
                List<String> args = new ArrayList<String>();
                args.addAll(Arrays.asList(koreCommand));
                args.addAll(Arrays.asList(
                        defPath,
                        "--module", moduleName,
                        "--pattern", pgmPath,
                        "--output", koreOutputFile.getAbsolutePath(),
                        "--searchType", searchType.toString(),
                        "--search", patternPath
                        )

                );
                if (depth.isPresent()) {
                    args.add("--depth");
                    args.add(depth.get().toString());
                }
                if (bound.isPresent()) {
                    args.add("--bound");
                    args.add(bound.get().toString());
                }
                if (options.experimental.smt.smtPrelude != null) {
                    args.add("--smt-prelude");
                    args.add(options.experimental.smt.smtPrelude);
                }
                koreCommand = args.toArray(koreCommand);
                if (haskellKRunOptions.dryRun) {
                    System.out.println(String.join(" ", koreCommand));
                    options.print.output = OutputModes.NONE;
                } else {
                    try {
                        File korePath = koreDirectory == null ? null : new File(koreDirectory);
                        if (executeCommandBasic(korePath, koreCommand) != 0) {
                            throw KEMException.criticalError("Haskell backend returned non-zero exit code");
                        }
                        TextToKore textToKore = new TextToKore();
                        Pattern kore = textToKore.parsePattern(koreOutputFile);
                        KoreToK koreToK = new KoreToK(idsToLabels, mod.sortAttributesFor(), StringUtil::enquoteKString);
                        K outputK = koreToK.apply(kore);
                        return outputK;
                    } catch (IOException e) {
                        throw KEMException.criticalError("I/O Error while executing", e);
                    } catch (InterruptedException e) {
                        throw KEMException.criticalError("Interrupted while executing", e);
                    } catch (ParseError parseError) {
                        throw KEMException.criticalError("Error parsing haskell backend output", parseError);
                    }
                }

                return initialConfiguration;
            }

            @Override
            public K prove(Module rules, Rule boundaryPattern) {
                String kompiledModule = KoreBackend.getKompiledString(module, def.topCellInitializer, files, false);
                files.saveToTemp("vdefinition.kore", kompiledModule);

                ModuleToKORE rulesConverter = new ModuleToKORE(rules, files, def.topCellInitializer);
                String koreOutput = rulesConverter.convertSpecificationModule(module, rules);
                files.saveToTemp("spec.kore", koreOutput);
                String defPath = files.resolveTemp("vdefinition.kore").getAbsolutePath();
                String specPath = files.resolveTemp("spec.kore").getAbsolutePath();
                String[] koreCommand = haskellKRunOptions.haskellBackendCommand.split("\\s+");
                String koreDirectory = haskellKRunOptions.haskellBackendHome;
                File koreOutputFile = files.resolveTemp("result.kore");
                List<String> args = new ArrayList<>();
                String defModuleName =
                        kProveOptions.defModule == null ? def.executionModule().name() : kProveOptions.defModule;
                String specModuleName = kProveOptions.specModule == null ? rules.name() : kProveOptions.specModule;

                args.addAll(Arrays.asList(koreCommand));
                args.addAll(Arrays.asList(
                        defPath,
                        "--module", defModuleName,
                        "--prove", specPath,
                        "--spec-module", specModuleName,
                        "--output", koreOutputFile.getAbsolutePath()));
                if (kProveOptions.depth != null) {
                    args.addAll(Arrays.asList(
                        "--depth", kProveOptions.depth.toString()));
                }
                if (options.experimental.smt.smtPrelude != null) {
                    args.add("--smt-prelude");
                    args.add(options.experimental.smt.smtPrelude);
                }
                koreCommand = args.toArray(koreCommand);
                if (haskellKRunOptions.dryRun) {
                    System.out.println(String.join(" ", koreCommand));
                    options.print.output = OutputModes.NONE;
                }
                System.out.println("Executing " + args);
                try {
                    File korePath = koreDirectory == null ? null : new File(koreDirectory);
                    if (executeCommandBasic(korePath, koreCommand) != 0) {
                        kem.registerCriticalWarning("Haskell backend returned non-zero exit code");
                    }
                    TextToKore textToKore = new TextToKore();
                    Pattern kore = textToKore.parsePattern(koreOutputFile);
                    KoreToK koreToK = new KoreToK(idsToLabels, rules.sortAttributesFor(), StringUtil::enquoteKString);
                    K outputK = koreToK.apply(kore);
                    return outputK;
                } catch (IOException e) {
                    throw KEMException.criticalError("I/O Error while executing", e);
                } catch (InterruptedException e) {
                    throw KEMException.criticalError("Interrupted while executing", e);
                } catch (ParseError parseError) {
                    throw KEMException.criticalError("Error parsing haskell backend output", parseError);
                }
            }

            @Override
            public boolean equivalence(Rewriter firstDef, Rewriter secondDef, Module firstSpec, Module secondSpec) {
                throw new UnsupportedOperationException();
            }
        };
    }

    private String getKoreString(K initialConfiguration, Module mod, ModuleToKORE converter) {
        ExpandMacros macroExpander = new ExpandMacros(mod, files, kompileOptions, false);
        K withMacros = macroExpander.expand(initialConfiguration);
        K kWithInjections = new AddSortInjections(mod).addInjections(withMacros);
        converter.convert(kWithInjections);
        return converter.toString();
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
        if (options.global.debug) {
            System.err.println("Executing command: " + String.join(" ", Arrays.asList(command)));
        }
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

    @DefinitionScoped
    public static class InitializeDefinition {
        final Properties serialized;

        @Inject
        public InitializeDefinition(FileUtil files) {
            try {
                FileInputStream input = new FileInputStream(files.resolveKompiled("kore_to_k_labels.properties"));
                serialized = new Properties();
                serialized.load(input);
            } catch (IOException e) {
                throw KEMException.criticalError("Error while loading Kore to K label map", e);
            }
        }
    }

}

