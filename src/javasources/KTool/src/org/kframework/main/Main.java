// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;

import org.fusesource.jansi.AnsiConsole;
import org.kframework.kagreg.KagregFrontEnd;
import org.kframework.kast.KastFrontEnd;
import org.kframework.kompile.KompileFrontEnd;
import org.kframework.krun.KRunFrontEnd;
import org.kframework.ktest.KTestFrontEnd;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;
import org.kframework.utils.file.KPaths;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Module;
import com.google.inject.ProvisionException;
import com.google.inject.spi.Message;

public class Main {

    /**
     * Sets the {@code java.library.path} system property to include the native libraries
     * directory containing extra Jar files distributed with K for this platform.
     */
    private static void setJavaLibraryPath() {
        System.setProperty("java.library.path", KPaths.getJavaLibraryPath());

        /* force java to reset the path (dirty hack) */
        try {
            Field fieldSysPath = ClassLoader.class.getDeclaredField("sys_paths");
            fieldSysPath.setAccessible(true);
            fieldSysPath.set(null, null);
        } catch (IllegalAccessException | NoSuchFieldException e) {
            e.printStackTrace();
        }
    }

    /**
     * @param args
     *            - the running arguments for the K3 tool. First argument must be one of the following: kompile|kast|krun.
     * @throws IOException when loadDefinition fails
     */
    public static void main(String[] args) {
        AnsiConsole.systemInstall();
        setJavaLibraryPath();

        Module[] modules;
        if (args.length >= 1) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
                switch (args[0]) {
                    case "-kompile":
                        modules = KompileFrontEnd.getModules(args2);
                        break;
                    case "-kagreg":
                        modules = KagregFrontEnd.getModules(args2);
                        break;
                    case "-kcheck":
                        assert false : "kcheck no longer supported";
                        return;
                    case "-ktest":
                        modules = KTestFrontEnd.getModules(args2);
                        break;
                    case "-kast":
                        modules = KastFrontEnd.getModules(args2);
                        break;
                    case "-krun":
                        modules = KRunFrontEnd.getModules(args2);
                        break;
                    case "-kpp":
                        modules = KppFrontEnd.getModules(args2);
                        break;
                    default:
                        invalidJarArguments();
                        return;
            }
            if (modules == null) {
                //boot error, we should have printed it already
                System.exit(1);
            }
            Injector injector = Guice.createInjector(modules);
            KExceptionManager kem = injector.getInstance(KExceptionManager.class);
            kem.installForUncaughtExceptions();
            try {
                boolean succeeded = injector.getInstance(FrontEnd.class).main();
                System.exit(succeeded ? 0 : 1);
            } catch (ProvisionException e) {
                kem.print();
                for (Message m : e.getErrorMessages()) {
                    if (!(m.getCause() instanceof KEMException)) {
                        throw e;
                    }
                }
                System.exit(1);
            }
        }
        invalidJarArguments();
    }

    private static void invalidJarArguments() {
        System.err.println("The first argument of K3 not recognized. Try -kompile, -kast, -krun, -ktest, or -kpp.");
        System.exit(1);
    }
}
