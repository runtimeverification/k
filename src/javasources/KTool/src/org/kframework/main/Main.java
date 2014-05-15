// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;

import org.fusesource.jansi.AnsiConsole;
import org.kframework.krun.K;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

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
    public static void main(String[] args) throws IOException {
        Stopwatch.instance();
        setJavaLibraryPath();
        AnsiConsole.systemInstall();

        boolean succeeded = true;
        if (args.length >= 1) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
            try {
                switch (args[0]) {
                    case "-kompile":
                        K.setTool(K.Tool.KOMPILE);
                        org.kframework.kompile.KompileFrontEnd.main(args2);
                        break;
                    case "-kagreg":
                        K.setTool(K.Tool.OTHER);
                        org.kframework.kagreg.KagregFrontEnd.kagreg(args2);
                        break;
                    case "-kcheck":
                        K.setTool(K.Tool.OTHER);
                        succeeded = org.kframework.kcheck.KCheckFrontEnd.kcheck(args2);
                        break;
                    case "-ktest":
                        K.setTool(K.Tool.KTEST);
                        succeeded = org.kframework.ktest.KTest.main(args2);
                        break;
                    case "-kast":
                        K.setTool(K.Tool.KAST);
                        succeeded = org.kframework.kast.KastFrontEnd.kast(args2);
                        break;
                    case "-krun":
                        K.setTool(K.Tool.KRUN);
                        succeeded = org.kframework.krun.KRunFrontEnd.execute_Krun(args2);
                        break;
                    case "-kpp":
                        K.setTool(K.Tool.OTHER);
                        Kpp.codeClean(args2);
                        break;
                    default:
                        invalidJarArguments();
                        break;
                }
            } catch (KEMException e) {
                // terminated with errors, so we need to return nonzero error code.
                GlobalSettings.kem.print();
                System.exit(1);
            }
             
            GlobalSettings.kem.print();
            System.exit(succeeded ? 0 : 1);
        }
        invalidJarArguments();
    }
    
    private static void invalidJarArguments() {
        System.err.println("The first argument of K3 not recognized. Try -kompile, -kast, -krun or -kpp.");
        System.exit(1);
    }
}
