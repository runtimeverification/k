// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.main;

import com.beust.jcommander.ParameterException;
import com.google.inject.Provider;
import org.kframework.utils.ExitOnTimeoutThread;
import org.kframework.utils.InterrupterRunnable;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;

public abstract class FrontEnd {

    protected abstract int run();

    private final KExceptionManager kem;
    protected final GlobalOptions globalOptions;
    private final String usage;
    private final JarInfo jarInfo;
    private final Provider<FileUtil> files;

    public FrontEnd(
            KExceptionManager kem,
            GlobalOptions globalOptions,
            String usage,
            JarInfo jarInfo,
            Provider<FileUtil> files) {
        this.kem = kem;
        this.globalOptions = globalOptions;
        this.usage = usage;
        this.jarInfo = jarInfo;
        this.files = files;
    }

    public int main() {
        int retval;
        try {
            if (globalOptions.help) {
                System.out.print(usage);
                retval = 0;
            } else if (globalOptions.version) {
                jarInfo.printVersionMessage();
                retval = 0;
            } else {
                if (globalOptions.timeout != null) {
                    new ExitOnTimeoutThread(globalOptions.timeout.toMillis()).start();
                }
                if (globalOptions.shutdownWaitTime != null && !Main.isNailgun()) {
                    //Will interrupt the thread on Ctrl+C and allow the backend to terminate gracefully.
                    Runtime.getRuntime().addShutdownHook(new Thread(new InterrupterRunnable(Thread.currentThread(),
                                    globalOptions.shutdownWaitTime.toMillis())));
                }
                try {
                    retval = run();
                } catch (ParameterException e) {
                    throw KEMException.criticalError(e.getMessage(), e);
                } finally {
                    files.get().deleteTempDir(kem);
                }
                kem.print();
            }
        } catch (KEMException e) {
            // terminated with errors, so we need to return nonzero error code.
            retval = KEMException.TERMINATED_WITH_ERRORS_EXIT_CODE;
            if (globalOptions.debug()) {
                e.printStackTrace();
            } else {
                kem.registerThrown(e);
            }
            kem.print();
        }
        return retval;
    }

    public static void printBootError(String message) {
        System.err.println(StringUtil.splitLines(KException.criticalError(message).toString()));
    }
}
