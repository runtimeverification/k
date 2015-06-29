// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.kframework.Rewriter;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.koreparser.KoreParser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

import static org.kframework.kore.KORE.*;

@DefinitionScoped
public class OcamlRewriter implements Function<Module, Rewriter> {

    private final FileUtil files;
    private final CompiledDefinition def;
    private final DefinitionToOcaml converter;

    @Inject
    public OcamlRewriter(KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions, CompiledDefinition def) {
        this.files = files;
        this.def = def;
        this.converter = new DefinitionToOcaml(kem, files, globalOptions, kompileOptions);
        converter.convert(def);
    }

    @Override
    public Rewriter apply(Module module) {
        if (!module.equals(def.executionModule())) {
            throw KEMException.criticalError("Invalid module specified for rewriting. Ocaml backend only supports rewriting over" +
                    " the definition's main module.");
        }
        return new Rewriter() {
            @Override
            public K execute(K k, Optional<Integer> depth) {
                String ocaml = converter.execute(k, depth.orElse(-1), files.resolveTemp("run.out").getAbsolutePath());
                files.saveToTemp("pgm.ml", ocaml);
                String output = compileAndExecOcaml("pgm.ml");
                return parseOcamlOutput(output);
            }

            @Override
            public List<Map<KVariable, K>> match(K k, Rule rule) {
                String ocaml = converter.match(k, rule, files.resolveTemp("run.out").getAbsolutePath());
                files.saveToTemp("match.ml", ocaml);
                String output = compileAndExecOcaml("match.ml");
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
        };
    }

    private K parseOcamlOutput(String output) {
        return KoreParser.parse(output, Source.apply(files.resolveTemp("run.out").getAbsolutePath()));
    }

    private String compileAndExecOcaml(String name) {
        try {
            ProcessBuilder pb = files.getProcessBuilder();
            if (DefinitionToOcaml.ocamlopt) {
                pb = pb.command("ocamlopt.opt", "-o", "a.out", "gmp.cmxa", "str.cmxa", "unix.cmxa", "-safe-string", files.resolveKompiled("def.cmx").getAbsolutePath(), "-I", "+gmp", "-I", files.resolveKompiled(".").getAbsolutePath(), name);
            } else {
                pb = pb.command("ocamlc.opt", "-o", "a.out", "-g", "gmp.cma", "str.cma", "unix.cma", "-safe-string", files.resolveKompiled("def.cmo").getAbsolutePath(), "-I", "+gmp", "-I", files.resolveKompiled(".").getAbsolutePath(), name);
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
                    while ((count = System.in.read(buffer)) > 0) {
                        p2.getOutputStream().write(buffer, 0, count);
                    }
                } catch (IOException | InterruptedException e) {}
            });
            Thread out = new Thread(() -> {
                int count;
                byte[] buffer = new byte[8192];
                try {
                    while ((count = p2.getInputStream().read(buffer)) >= 0) {
                        System.out.write(buffer, 0, count);
                    }
                } catch (IOException e) {}
            });
            Thread err = new Thread(() -> {
                int count;
                byte[] buffer = new byte[8192];
                try {
                    while ((count = p2.getErrorStream().read(buffer)) >= 0) {
                        System.err.write(buffer, 0, count);
                    }
                } catch (IOException e) {}
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
}
