// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.kframework.Rewriter;
import org.kframework.RewriterResult;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.krun.KRunOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.koreparser.KoreParser;
import scala.Tuple2;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.kore.KORE.*;

@RequestScoped
public class OcamlRewriter implements Function<Module, Rewriter> {

    private final FileUtil files;
    private final CompiledDefinition def;
    private final DefinitionToOcaml converter;
    private final KRunOptions options;

    @Inject
    public OcamlRewriter(
            KExceptionManager kem,
            FileUtil files,
            GlobalOptions globalOptions,
            KompileOptions kompileOptions,
            CompiledDefinition def,
            InitializeDefinition init,
            KRunOptions options) {
        this.files = files;
        this.def = def;
        this.converter = new DefinitionToOcaml(kem, files, globalOptions, kompileOptions, null);
        converter.initialize(init.serialized, def);
        this.options = options;
    }

    @Override
    public Rewriter apply(Module module) {
        if (!module.equals(def.executionModule())) {
            throw KEMException.criticalError("Invalid module specified for rewriting. Ocaml backend only supports rewriting over" +
                    " the definition's main module.");
        }
        return new Rewriter() {
            @Override
            public RewriterResult execute(K k, Optional<Integer> depth) {
                String ocaml = converter.execute(k, depth.orElse(-1), files.resolveTemp("run.out").getAbsolutePath());
                files.saveToTemp("pgm.ml", ocaml);
                String output = compileAndExecOcaml("pgm.ml");
                return new RewriterResult(Optional.<Integer>empty(), parseOcamlOutput(output));
            }

            @Override
            public List<Map<KVariable, K>> match(K k, Rule rule) {
                String ocaml = converter.match(k, rule, files.resolveTemp("run.out").getAbsolutePath());
                files.saveToTemp("match.ml", ocaml);
                String output = compileAndExecOcaml("match.ml");
                return parseOcamlSearchOutput(output);
            }

            @Override
            public Tuple2<K, List<? extends Map<? extends KVariable, ? extends K>>> executeAndMatch(K k, Optional<Integer> depth, Rule rule) {
                String ocaml = converter.executeAndMatch(k, depth.orElse(-1), rule, files.resolveTemp("run.out").getAbsolutePath(), files.resolveTemp("run.subst").getAbsolutePath());
                files.saveToTemp("pgm.ml", ocaml);
                String output = compileAndExecOcaml("pgm.ml");
                String subst = files.loadFromTemp("run.subst");
                return Tuple2.apply(parseOcamlOutput(output), parseOcamlSearchOutput(subst));
            }

            @Override
            public List<? extends Map<? extends KVariable, ? extends K>> search(K initialConfiguration, Optional<Integer> depth, Optional<Integer> bound, Rule pattern) {
                throw new UnsupportedOperationException();
            }
        };
    }

    private List<Map<KVariable, K>> parseOcamlSearchOutput(String output) {
        String[] lines = output.split("\n");
        int count = Integer.parseInt(lines[0]);
        int line = 1;
        List<Map<KVariable, K>> list = new ArrayList<>();
        for (int i = 0; i < count; i++) {
            Map<KVariable, K> map = new HashMap<>();
            list.add(map);
            for (; line < lines.length; line += 2) {
                if (lines[line].equals("|")) {
                    line++;
                    break;
                }
                KVariable key = KVariable(lines[line]);
                K value = parseOcamlOutput(lines[line+1]);
                map.put(key, value);
            }
        }
        return list;
    }

    private K parseOcamlOutput(String output) {
        return KoreParser.parse(output, Source.apply(files.resolveTemp("run.out").getAbsolutePath()));
    }

    private String compileAndExecOcaml(String name) {
        try {
            ProcessBuilder pb = files.getProcessBuilder();
            List<String> args = new ArrayList<>(Arrays.asList("-g", "-o", "a.out", "-package", "gmp", "-package", "zarith",
                    "-package", "str", "-package", "unix", "-linkpkg", "-safe-string"));
            args.addAll(0, converter.options.packages.stream().flatMap(p -> Stream.of("-package", p)).collect(Collectors.toList()));
            args.addAll(options.experimental.nativeLibraries.stream().flatMap(lib -> Stream.of("-cclib", "-l" + lib)).collect(Collectors.toList()));
            if (converter.options.ocamlopt) {
                args.add(0, "ocamlfind");
                args.add(1, "ocamlopt");
                if (!converter.options.noLinkPrelude) {
                    args.add(files.resolveKompiled("constants.cmx").getAbsolutePath());
                    args.add(files.resolveKompiled("prelude.cmx").getAbsolutePath());
                }
                args.addAll(Arrays.asList(files.resolveKompiled("def.cmx").getAbsolutePath(), "-I", files.resolveKompiled(".").getAbsolutePath(),
                        files.resolveKompiled("parser.cmx").getAbsolutePath(), files.resolveKompiled("lexer.cmx").getAbsolutePath(),
                        name));
                args.add("-inline");
                args.add("20");
                args.add("-nodynlink");
                pb = pb.command(args);
                pb.environment().put("OCAMLFIND_COMMANDS", "ocamlopt=ocamlopt.opt");
            } else {
                args.add(0, "ocamlfind");
                args.add(1, "ocamlc");
                if (!converter.options.noLinkPrelude) {
                    args.add(files.resolveKompiled("constants.cmo").getAbsolutePath());
                    args.add(files.resolveKompiled("prelude.cmo").getAbsolutePath());
                }
                args.addAll(Arrays.asList(files.resolveKompiled("def.cmo").getAbsolutePath(), "-I", files.resolveKompiled(".").getAbsolutePath(),
                        files.resolveKompiled("parser.cmo").getAbsolutePath(), files.resolveKompiled("lexer.cmo").getAbsolutePath(),
                        name));
                pb = pb.command(args);
                pb.environment().put("OCAMLFIND_COMMANDS", "ocamlc=ocamlc.opt");
            }
            Process p = pb.directory(files.resolveTemp("."))
                    .redirectError(files.resolveTemp("compile.err"))
                    .redirectOutput(files.resolveTemp("compile.out"))
                    .start();
            int exit = p.waitFor();
            if (exit != 0) {
                System.err.println(files.loadFromTemp("compile.err"));
                throw KEMException.criticalError("Failed to compile program to ocaml. See output for error information.");
            }
            Process p2 = files.getProcessBuilder()
                    .command(files.resolveTemp("a.out").getAbsolutePath())
                    .start();

            Thread in = new Thread(() -> {
                int count;
                byte[] buffer = new byte[8192];
                try {
                    while (true) {
                        if (System.in.available() > 0) {
                            count = System.in.read(buffer);
                            if (count < 0)
                                break;
                            p2.getOutputStream().write(buffer, 0, count);
                        } else {
                            Thread.sleep(100);
                        }
                    }
                } catch (IOException | InterruptedException e) {}
            });
            Thread out = new Thread(() -> {
                int count;
                byte[] buffer = new byte[8192];
                try {
                    while (true) {
                        count = p2.getInputStream().read(buffer);
                        if (count < 0)
                            break;
                        System.out.write(buffer, 0, count);
                        if (p2.getInputStream().available() == 0)
                            Thread.sleep(100);
                    }
                } catch (IOException | InterruptedException e) {}
            });
            Thread err = new Thread(() -> {
                int count;
                byte[] buffer = new byte[8192];
                try {
                    while (true) {
                        count = p2.getErrorStream().read(buffer);
                        if (count < 0)
                            break;
                        System.err.write(buffer, 0, count);
                        if (p2.getErrorStream().available() == 0)
                            Thread.sleep(100);
                    }
                } catch (IOException | InterruptedException e) {}
            });
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
            if (exit != 0) {
                throw KEMException.criticalError("Failed to execute program in ocaml. See output for error information.");
            }
            return files.loadFromTemp("run.out");
        } catch (IOException e) {
            throw KEMException.criticalError("Failed to start ocamlopt: " + e.getMessage(), e);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw KEMException.criticalError("Ocaml process interrupted.", e);
        }
    }

    @DefinitionScoped
    public static class InitializeDefinition {
        private final DefinitionToOcaml serialized;

        @Inject
        public InitializeDefinition(BinaryLoader loader, FileUtil files) {
            serialized = loader.loadOrDie(DefinitionToOcaml.class, files.resolveKompiled("ocaml_converter.bin"));
        }
    }
}
