// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.File;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

import com.beust.jcommander.ParameterException;

public abstract class FrontEnd {

    protected abstract boolean run();

    private final KExceptionManager kem;
    private final GlobalOptions globalOptions;
    private final String usage, experimentalUsage;
    private final JarInfo jarInfo;
    private final FileUtil files;

    public FrontEnd(
            KExceptionManager kem,
            GlobalOptions globalOptions,
            String usage,
            String experimentalUsage,
            JarInfo jarInfo,
            FileUtil files) {
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.usage = usage;
        this.experimentalUsage = experimentalUsage;
        this.jarInfo = jarInfo;
        this.files = files;
    }

    public boolean main() {
        boolean succeeded = true;
        try {
            if (globalOptions.help) {
                System.out.print(usage);
            } else if (globalOptions.helpExperimental) {
                System.out.print(experimentalUsage);
            } else if (globalOptions.version) {
                jarInfo.printVersionMessage();
            } else {
                try {
                    succeeded = run();
                } catch (ParameterException e) {
                    throw KExceptionManager.criticalError(e.getMessage(), e);
                } finally {
                    files.deleteTempDir();
                }
                kem.print();
            }
        } catch (KExceptionManager.KEMException e) {
            // terminated with errors, so we need to return nonzero error code.
            succeeded = false;
            if (globalOptions.debug) {
                e.printStackTrace();
            }
            e.register(kem);
            kem.print();
        }
        return succeeded;
    }

    public static void printBootError(String message) {
        System.err.println(StringUtil.splitLines(KException.criticalError(message).toString()));
    }
}
