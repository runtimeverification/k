// Copyright (c) 2015-2019 Runtime Verification, Inc. (RV-Match team). All Rights Reserved.
package org.kframework.backend.ocaml;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.kframework.compile.Backend;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
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
        files.saveToKompiled("realdef.ml", ocaml);
        new BinaryLoader(kem).saveOrDie(files.resolveKompiled("ocaml_converter.bin"), def);
        try {
            FileUtils.copyFile(files.resolveKBase("include/ocaml/prelude.ml"), files.resolveKompiled("prelude.ml"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/lexer.mll"), files.resolveKompiled("lexer.mll"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/parser.mly"), files.resolveKompiled("parser.mly"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/hooks.ml"), files.resolveKompiled("hooks.ml"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/run.ml"), files.resolveKompiled("run.ml"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/marshalvalue.ml"), files.resolveKompiled("marshalvalue.ml"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/plugin.ml"), files.resolveKompiled("plugin.ml"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/load_terms.c"), files.resolveKompiled("load_terms.c"));
            FileUtils.copyFile(files.resolveKBase("include/ocaml/fake_load_terms.c"), files.resolveKompiled("fake_load_terms.c"));
            String execution_pmg_ocaml = def.ocamlCompile(compiledDefinition.topCellInitializer, compiledDefinition.exitCodePattern, options.dumpExitCode);
            files.saveToKompiled("execution_pgm.ml", execution_pmg_ocaml);

            ProcessBuilder pb = files.getProcessBuilder();
            int exit = pb.command("ocamllex", "-q", "lexer.mll").directory(files.resolveKompiled(".")).inheritIO().start().waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("ocamllex returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
            exit = pb.command("ocamlyacc", "parser.mly").directory(files.resolveKompiled(".")).inheritIO().start().waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("ocamlyacc returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
            List<String> args = new ArrayList<>(Arrays.asList("-c", "-g", "-package", "gmp", "-package", "zarith", "-package", "uuidm",
                "-safe-string", "-w", "a-4-6-11-26-27-44", "-match-context-rows", "2", "constants.ml", "prelude.ml", "plugin.ml", "parser.mli", "parser.ml", "lexer.ml", "hooks.ml", "run.ml", "realdef.ml"));
            args.addAll(2, options.packages.stream().flatMap(p -> Stream.of("-package", p)).collect(Collectors.toList()));
            if (!options.genMLOnly) {
                String ocamlfind = getOcamlFind(files);
                String libExt;
                String sharedLibExt;
                String flag;
                String ext;
                if (options.ocamlopt()) {
                    args.add(0, ocamlfind);
                    args.add(1, "ocamlopt");
                    args.add("-inline");
                    args.add("20");
                    pb.command(args);
                    libExt = "cmxa";
                    sharedLibExt = "cmxs";
                    flag = "-shared";
                    ext = "cmx";
                } else {
                    args.add(0, ocamlfind);
                    args.add(1, "ocamlc");
                    pb.command(args);
                    libExt = "cma";
                    sharedLibExt = "cma";
                    flag = "-a";
                    ext = "cmo";
                }
                Process p = pb
                        .directory(files.resolveKompiled("."))
                        .inheritIO()
                        .start();

                exit = p.waitFor();
                if (exit != 0) {
                    throw KEMException.criticalError("ocamlopt returned nonzero exit code: " + exit + "\nExamine output to see errors.");
                }

                args.clear();
                args.addAll(Arrays.asList("-g", flag, "-o", "realdef." + sharedLibExt, "realdef." + ext));
                args.addAll(3, options.packages.stream().flatMap(pkg -> Stream.of("-package", pkg)).collect(Collectors.toList()));
                args.add(0, ocamlfind);
                if (options.ocamlopt()) {
                    args.add(1, "ocamlopt");
                } else {
                    args.add(1, "ocamlc");
                }
                pb.command(args);
                p = pb.start();

                exit = p.waitFor();
                if (exit != 0) {
                    throw KEMException.criticalError("ocamlopt returned nonzero exit code: " + exit + "\nExamine output to see errors.");
                }

                OcamlRewriter rewriter = new OcamlRewriter(files, def, new KRunOptions());
                ocaml = def.interpreter();
                files.saveToTemp("interpreter.ml", ocaml);
                rewriter.compileOcaml("interpreter.ml");
                files.resolveTemp("a.out").renameTo(files.resolveKompiled("interpreter"));
                files.resolveKompiled("interpreter").setExecutable(true);
            } else {
                // write out the interpreter program
                ocaml = def.interpreter();
                files.saveToKompiled("interpreter.ml", ocaml);
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw KEMException.criticalError("Ocaml process interrupted.", e);
        } catch (IOException e) {
            throw KEMException.criticalError("Error starting ocamlopt process: " + e.getMessage(), e);
        }
    }

    public static String getOcamlFind(FileUtil files) {
        String ocamlfind = "ocamlfind";
        String env = files.getEnv().get("K_OCAML_HOME");
        if (env != null) {
            ocamlfind = new File(files.resolveWorkingDirectory(env), "ocamlfind").getAbsolutePath();
        }
        return ocamlfind;
    }

    @Override
    public Function<Definition, Definition> steps() {
        return Kompile.defaultSteps(kompileOptions, kem, files);
    }

    @Override
    public Function<Module, Module> specificationSteps(Definition ignored) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Set<String> excludedModuleTags() {
        return new HashSet<>(Arrays.asList("symbolic", "kore"));
    }
}
