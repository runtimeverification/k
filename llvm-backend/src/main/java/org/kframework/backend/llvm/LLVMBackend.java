// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.llvm;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.mutable.MutableInt;
import org.kframework.attributes.Att;
import org.kframework.backend.llvm.matching.Matching;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.compile.Backend;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

public class LLVMBackend extends KoreBackend {

    private final GlobalOptions globalOptions;
    private final LLVMKompileOptions options;
    private final KExceptionManager kem;
    private final KompileOptions kompileOptions;
    private final Tool tool;

    @Inject
    public LLVMBackend(
            KompileOptions kompileOptions,
            GlobalOptions globalOptions,
            FileUtil files,
            KExceptionManager kem,
            LLVMKompileOptions options,
            Tool tool) {
        super(kompileOptions, files, kem, tool);
        this.globalOptions = globalOptions;
        this.options = options;
        this.kompileOptions = kompileOptions;
        this.kem = kem;
        this.tool = tool;
    }


    @Override
    public void accept(Backend.Holder h) {
        Stopwatch sw = new Stopwatch(globalOptions);
        String kore = getKompiledString(h.def, true);
        h.def = null;
        files.saveToKompiled("definition.kore", kore);
        sw.printIntermediate("  Print definition.kore");
        FileUtils.deleteQuietly(files.resolveKompiled("dt"));
        MutableInt warnings = new MutableInt();
        boolean optimize = kompileOptions.optimize1 || kompileOptions.optimize2 || kompileOptions.optimize3;
        Matching.writeDecisionTreeToFile(
                files.resolveKompiled("definition.kore"),
                options.heuristic,
                files.resolveKompiled("dt"),
                Matching.getThreshold(getThreshold()),
                !optimize,
                globalOptions.includesExceptionType(ExceptionType.USELESS_RULE),
                options.enableSearch,
                ex -> {
          kem.addKException(ex);
          if (globalOptions.includesExceptionType(ex.getType())) {
              warnings.increment();
          }
          return null;
        });
        sw.printIntermediate("  Write decision tree");
        if (warnings.intValue() > 0 && kem.options.warnings2errors) {
          throw KEMException.compilerError("Had " + warnings.intValue() + " pattern matching errors.");
        }
        if (options.noLLVMKompile) {
            return;
        }
        if (options.enableSearch && options.llvmKompileOutput != null) {
            throw KEMException.criticalError("Can't use --llvm-kompile-output with --enable-search.");
        }
        if (options.llvmKompileType.equals("python") && options.llvmKompileOutput != null) {
            throw KEMException.criticalError("Can't use --llvm-kompile-output with --llvm-kompile-type python");
        }
        String llvmType;
        switch (options.llvmKompileType) {
            case "main":
            case "search":
            case "static":
            case "library":
            case "python":
            case "c":
                llvmType = options.llvmKompileType;
                break;
            default:
                throw KEMException.criticalError("Non-valid argument for --llvm-kompile-type: " + options.llvmKompileType + ". Expected [main|search|library|static|python|c]");
        }

        String llvmOutput = "interpreter";
        if (options.llvmKompileOutput != null) {
            llvmOutput = options.llvmKompileOutput;
        }

        if (options.llvmKompileType.equals("python")) {
            llvmOutput = null;
        }

        llvmKompile(llvmType, llvmOutput);

        if (options.enableSearch) {
            llvmKompile("search", "search");
        }
    }

    private void llvmKompile(String type, String executable) {
        Stopwatch sw = new Stopwatch(globalOptions);
        ProcessBuilder pb = files.getProcessBuilder();
        List<String> args = new ArrayList<>();

        try {
            args.add("llvm-kompile");
            args.add(files.resolveKompiled("definition.kore").getCanonicalPath());
            args.add(files.resolveKompiled("dt").getCanonicalPath());
            args.add(type);

            // Arguments after this point are passed on to Clang.
            args.add("--");

            if (options.debug) {
                args.add("-g");
                args.add("-O1");
            }

            // For Python bindings, we explicitly leave this unset so that python3-config
            // can decide the proper filename.
            if (executable != null) {
                args.add("-o");

                File outputFile = new File(executable);
                if(!new File(executable).isAbsolute()) {
                    outputFile = files.resolveKompiled(executable);
                }

                args.add(outputFile.getCanonicalPath());
            }

            if (!options.debug) {
                if (kompileOptions.optimize1) args.add("-O1");
                if (kompileOptions.optimize2) args.add("-O2");
                if (kompileOptions.optimize3) args.add("-O2"); // clang -O3 does not make the llvm backend any faster
            }

            args.addAll(options.ccopts);

            if (globalOptions.verbose) {
                System.out.println("  \u250cExecuting: " + String.join(" ", args));
            }

            Process p = pb.command(args).inheritIO().start();
            int exit = p.waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("llvm-kompile returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
        } catch (IOException | InterruptedException e) {
            throw KEMException.criticalError("Error with I/O while executing llvm-kompile", e);
        }
        sw.printIntermediate("  \u2514" + executable + ": " + type);
    }

    private String getThreshold() {
        if (!options.iterated && !kompileOptions.optimize3) {
            return "0";
        }
        return options.iteratedThreshold;
    }

    @Override
    public Set<Att.Key> excludedModuleTags() {
        return new HashSet<>(Arrays.asList(Att.SYMBOLIC(), Att.KAST()));
    }
}
