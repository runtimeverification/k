// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.haskell;

import com.google.inject.Inject;
import org.kframework.attributes.Att;
import org.kframework.backend.kore.KoreBackend;
import org.kframework.compile.Backend;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.EnumSet;
import java.util.HashSet;

import static org.kframework.compile.ResolveHeatCoolAttribute.Mode.*;

public class HaskellBackend extends KoreBackend {

    private final KompileOptions kompileOptions;
    private final GlobalOptions globalOptions;
    private final FileUtil files;
    private final HaskellKompileOptions haskellKompileOptions;

    @Inject
    public HaskellBackend(
            KompileOptions kompileOptions,
            GlobalOptions globalOptions,
            HaskellKompileOptions haskellKompileOptions,
            FileUtil files,
            KExceptionManager kem,
            Tool tool) {
        super(kompileOptions, files, kem, EnumSet.of(HEAT_RESULT, COOL_RESULT_CONDITION), false, tool);
        this.files = files;
        this.haskellKompileOptions = haskellKompileOptions;
        this.kompileOptions = kompileOptions;
        this.globalOptions = globalOptions;
    }


    @Override
    public void accept(Backend.Holder h) {
        Stopwatch sw = new Stopwatch(globalOptions);
        String kore = getKompiledString(h.def, true);
        h.def = null;
        files.saveToKompiled("definition.kore", kore);
        sw.printIntermediate("  Print definition.kore");
        ProcessBuilder pb = files.getProcessBuilder();
        List<String> args = new ArrayList<>();
        if (haskellKompileOptions.noHaskellBinary) {
            args.add("kore-parser");
            args.add("--no-print-definition");
            args.add("definition.kore");
        } else {
            args.add(haskellKompileOptions.haskellBackendCommand);
            args.add("definition.kore");
            args.add("--module");
            args.add(kompileOptions.mainModule(files));
            args.add("--output");
            args.add("haskellDefinition.bin");
            args.add("--serialize");
        }
        try {
          Process p = pb.command(args).directory(files.resolveKompiled(".")).inheritIO().start();
          int exit = p.waitFor();
          if (exit != 0) {
              throw KEMException.criticalError("Haskell backend reported errors validating compiled definition.\nExamine output to see errors.");
          }
        } catch (IOException | InterruptedException e) {
            throw KEMException.criticalError("Error with I/O while executing kore-parser", e);
        }
        sw.printIntermediate("  Validate def");
    }

    @Override
    public Set<Att.Key> excludedModuleTags() {
        return new HashSet<>(Arrays.asList(Att.CONCRETE(), Att.KAST()));
    }
}
