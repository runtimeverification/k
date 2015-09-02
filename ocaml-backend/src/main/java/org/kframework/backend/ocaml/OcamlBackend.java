// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.kframework.definition.Definition;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.compile.Backend;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by dwightguth on 5/27/15.
 */
public class OcamlBackend implements Backend {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final GlobalOptions globalOptions;
    private final KompileOptions kompileOptions;
    private final OcamlOptions options;

    @Inject
    public OcamlBackend(KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions, OcamlOptions options) {
        this.kem = kem;
        this.files = files;
        this.globalOptions = globalOptions;
        this.kompileOptions = kompileOptions;
        this.options = options;
    }

    @Override
    public void accept(CompiledDefinition compiledDefinition) {
        DefinitionToOcaml def = new DefinitionToOcaml(kem, files, globalOptions, kompileOptions, options);
        def.initialize(compiledDefinition);
        String ocaml = def.constants();
        files.saveToKompiled("constants.ml", ocaml);
        ocaml = def.definition();
        files.saveToKompiled("def.ml", ocaml);
        new BinaryLoader(kem).saveOrDie(files.resolveKompiled("ocaml_converter.bin"), def);
        try {
            FileUtils.copyFile(files.resolveKBase("include/ocaml/prelude.ml"), files.resolveKompiled("prelude.ml"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/lexer.mll"), files.resolveKompiled("lexer.mll"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/parser.mly"), files.resolveKompiled("parser.mly"));
            ProcessBuilder pb = files.getProcessBuilder();
            int exit = pb.command("ocamllex", "lexer.mll").directory(files.resolveKompiled(".")).inheritIO().start().waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("ocamllex returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
            exit = pb.command("ocamlyacc", "parser.mly").directory(files.resolveKompiled(".")).inheritIO().start().waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("ocamlyacc returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
            List<String> args = new ArrayList<>(Arrays.asList("-c", "-g", "-package", "gmp", "-package", "zarith",
                "-safe-string", "-w", "-26-11", "constants.ml", "prelude.ml", "def.ml", "parser.mli", "parser.ml", "lexer.ml"));
            args.addAll(2, options.packages.stream().flatMap(p -> Stream.of("-package", p)).collect(Collectors.toList()));
            if (!options.genMLOnly) {
                if (options.ocamlopt) {
                    args.add(0, "ocamlfind");
                    args.add(1, "ocamlopt");
                    args.add("-inline");
                    args.add("20");
                    args.add("-nodynlink");
                    pb.command(args).environment().put("OCAMLFIND_COMMANDS", "ocamlopt=ocamlopt.opt");
                } else {
                    args.add(0, "ocamlfind");
                    args.add(1, "ocamlc");
                    pb.command(args).environment().put("OCAMLFIND_COMMANDS", "ocamlc=ocamlc.opt");
                }
                Process ocamlopt = pb
                        .directory(files.resolveKompiled("."))
                        .inheritIO()
                        .start();
                exit = ocamlopt.waitFor();
                if (exit != 0) {
                    throw KEMException.criticalError("ocamlopt returned nonzero exit code: " + exit + "\nExamine output to see errors.");
                }
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw KEMException.criticalError("Ocaml process interrupted.", e);
        } catch (IOException e) {
            throw KEMException.criticalError("Error starting ocamlopt process: " + e.getMessage(), e);
        }
    }

    @Override
    public Function<Definition, Definition> steps(Kompile kompile) {
        return kompile.defaultSteps();
    }
}
