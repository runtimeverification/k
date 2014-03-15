package org.kframework.main;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;

import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.Error;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.KPaths;

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
     * @throws TransformerException when loadDefinition fails
     * @throws IOException when loadDefinition fails 
     */
    public static void main(String[] args) throws IOException, TransformerException {
        Stopwatch.instance();
        setJavaLibraryPath();

        if (args.length >= 1) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
            switch (args[0]) {
                case "-kompile":
                    org.kframework.kompile.KompileFrontEnd.main(args2);
                    break;
                case "-kagreg":
                    org.kframework.kagreg.KagregFrontEnd.kagreg(args2);
                    break;
                case "-kcheck":
                    org.kframework.kcheck.KCheckFrontEnd.kcheck(args2);
                    break;
                case "-ktest":
                    org.kframework.ktest.KTest.main(args2);
                    break;
                case "-kast":
                    org.kframework.kast.KastFrontEnd.kast(args2);
                    break;
                case "-krun":
                    // unable to load commandlineOptions since it loads K class
                    // K loads Color which sets headless field in GraphicsEnvironment
                    // and since this can be set only once we can not reset it by java.awt.headless
                    for (String s : args) {
                        if (s.contains("debug-gui")) {
                            System.setProperty("java.awt.headless", "false");
                            //force headless filed to be instantiated
                            java.awt.GraphicsEnvironment.isHeadless();
                            break;
                        }
                    }
                    org.kframework.krun.Main.execute_Krun(args2);
                    break;
                case "-kpp":
                    Kpp.codeClean(args2);
                    break;
                default:
                    Error.report("The first argument of K3 not recognized. Try -kompile, -kast, -krun or -kpp.");
                    break;
            }
            
            System.exit(0);
        } else
            Error.report("There must be a first argument to K3: try -kompile, -kast, -krun or -kpp.");
    }
}
