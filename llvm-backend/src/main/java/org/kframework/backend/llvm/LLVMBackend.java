// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.backend.llvm;

import com.google.inject.Inject;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class LLVMBackend extends KoreBackend {

    private final LLVMKompileOptions options;

    @Inject
    public LLVMBackend(
            KompileOptions kompileOptions,
            FileUtil files,
            KExceptionManager kem,
            LLVMKompileOptions options) {
        super(kompileOptions, files, kem);
        this.options = options;
    }


    @Override
    public void accept(CompiledDefinition def) {
        String kore = getKompiledString(def);
        files.saveToKompiled("definition.kore", kore);
        ProcessBuilder pb = files.getProcessBuilder();
        List<String> args = new ArrayList<>();
        args.add("llvm-kompile");
        args.add("definition.kore");
        args.add(def.kompiledDefinition.mainModule().name());
        args.add("-o");
        args.add("interpreter");
        args.addAll(options.ccopts);
        try {
            Process p = pb.command(args).directory(files.resolveKompiled(".")).inheritIO().start();
            int exit = p.waitFor();
            if (exit != 0) {
                throw KEMException.criticalError("llvm-kompile returned nonzero exit code: " + exit + "\nExamine output to see errors.");
            }
        } catch (IOException | InterruptedException e) {
            throw KEMException.criticalError("Error with I/O while executing llvm-kompile", e);
        }
    }

}
