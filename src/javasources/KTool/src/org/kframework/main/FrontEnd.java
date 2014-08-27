// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.main;

import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;

public abstract class FrontEnd {

    protected abstract boolean run();

    private final KExceptionManager kem;
    private final GlobalOptions globalOptions;
    private final String usage, experimentalUsage;

    public FrontEnd(
            KExceptionManager kem,
            GlobalOptions globalOptions,
            String usage,
            String experimentalUsage) {
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.usage = usage;
        this.experimentalUsage = experimentalUsage;
    }

    public boolean main() {
        boolean succeeded = true;
        try {
            if (globalOptions.help) {
                System.out.print(usage);
            } else if (globalOptions.helpExperimental) {
                System.out.print(experimentalUsage);
            } else if (globalOptions.version) {
                String msg = FileUtil.getFileContent(KPaths.getKBase(false) + KPaths.VERSION_FILE);
                System.out.print(msg);
            } else {
                succeeded = run();
                kem.print();
            }
        } catch (KExceptionManager.KEMException e) {
            // terminated with errors, so we need to return nonzero error code.
            succeeded = false;
            kem.print(e);
        }
        return succeeded;
    }

    public static void printBootError(String message) {
        System.err.println(StringUtil.splitLines(KException.criticalError(message).toString()));
    }
}
