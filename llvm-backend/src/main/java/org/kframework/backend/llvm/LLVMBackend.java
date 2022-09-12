// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.backend.llvm;

import com.google.inject.Inject;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.mutable.MutableInt;
import org.kframework.backend.llvm.matching.Matching;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.compile.Backend;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
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
        String kore = getKompiledString(h.def);
        h.def = null;
        files.saveToKompiled("definition.kore", kore);
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
        if (warnings.intValue() > 0 && kem.options.warnings2errors) {
          throw KEMException.compilerError("Had " + warnings.intValue() + " pattern matching errors.");
        }
        if (options.noLLVMKompile) {
            return;
        }
        if (options.enableSearch && options.llvmKompileOutput != null) {
            throw KEMException.criticalError("Can't use --llvm-kompile-output with --enable-search.");
        }
        String llvmType;
        switch (options.llvmKompileType) {
            case "main":
            case "search":
            case "library":
            case "static":
                llvmType = options.llvmKompileType;
                break;
            default:
                throw KEMException.criticalError("Non-valid argument for --llvm-kompile-type: " + options.llvmKompileType + ". Expected [main|search|library|static]");
        }

        String llvmOutput = "interpreter";
        if (options.llvmKompileOutput != null) {
            llvmOutput = options.llvmKompileOutput;
        }
        llvmKompile(llvmType, llvmOutput);

        if (options.enableSearch) {
            llvmKompile("search", "search");
        }
    }

    private void llvmKompile(String type, String executable) {
        ProcessBuilder pb = files.getProcessBuilder();
        List<String> args = new ArrayList<>();
        args.add("llvm-kompilex");
        args.add("definition.kore");
        args.add("dt");
        args.add(type);

        // Arguments after this point are passed on to Clang.
        args.add("--");

        args.add("-o");
        args.add(executable);
        if (kompileOptions.optimize1) args.add("-O1");
        if (kompileOptions.optimize2) args.add("-O2");
        if (kompileOptions.optimize3) args.add("-O2"); // clang -O3 does not make the llvm backend any faster
        args.addAll(options.ccopts);
        try {
            File kompiledDir = files.resolveKompiled(".");

            if (globalOptions.verbose) {
                System.out.println("Executing in " + kompiledDir.getCanonicalPath() + ": " + String.join(" ", args));
            }

            Process p = pb.command(args).directory(kompiledDir).inheritIO().start();
            int exit = p.waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("llvm-kompilex returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
        } catch (IOException | InterruptedException e) {
            throw KEMException.criticalError("Error with I/O while executing llvm-kompilex", e);
        }
    }

    private String getThreshold() {
        if (!options.iterated && !kompileOptions.optimize3) {
            return "0";
        }
        return options.iteratedThreshold;
    }

    @Override
    public Set<String> excludedModuleTags() {
        return new HashSet<>(Arrays.asList("symbolic", "kast"));
    }
}
