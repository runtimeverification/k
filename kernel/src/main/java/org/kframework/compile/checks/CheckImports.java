package org.kframework.compile.checks;

import org.kframework.definition.Module;
import org.kframework.utils.errorsystem.KExceptionManager;

public class CheckImports {

    private final KExceptionManager kem;

    public CheckImports(Module mainModule, KExceptionManager kem) {
        this.kem = kem;
    }

    public void check(Module m) {
        if (false) {
            kem.registerCompilerWarning("Error message");
        }
    }
}
