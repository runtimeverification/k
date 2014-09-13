// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.ServiceLoader;

import org.apache.commons.io.FilenameUtils;
import org.fusesource.jansi.AnsiConsole;
import org.kframework.kagreg.KagregFrontEnd;
import org.kframework.kast.KastFrontEnd;
import org.kframework.kompile.KompileFrontEnd;
import org.kframework.krun.KRunFrontEnd;
import org.kframework.ktest.KTestFrontEnd;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Module;
import com.google.inject.ProvisionException;
import com.google.inject.spi.Message;
import org.kframework.utils.file.JarInfo;

public class Main {

    /**
     * @param args
     *            - the running arguments for the K3 tool. First argument must be one of the following: kompile|kast|krun.
     * @throws IOException when loadDefinition fails
     */
    public static void main(String[] args) {
        AnsiConsole.systemInstall();

        KPluginClassLoader loader = new KPluginClassLoader();
        loader.addPath(
                FilenameUtils.concat(JarInfo.getKBase(false),
                        FilenameUtils.concat("lib", "plugins")));

        ServiceLoader<KModule> kLoader = ServiceLoader.load(KModule.class, loader);
        List<KModule> kModules = new ArrayList<>();
        for (KModule m : kLoader) {
            kModules.add(m);
        }

        List<Module> modules = new ArrayList<>(0);
        if (args.length >= 1) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
                switch (args[0]) {
                    case "-kompile":
                        modules.addAll(Arrays.asList(KompileFrontEnd.getModules(args2)));
                        for (KModule kModule : kModules) {
                            List<Module> ms = kModule.getKompileModules();
                            if (ms != null) {
                                modules.addAll(ms);
                            }
                        }
                        break;
                    case "-kagreg":
                        modules = Arrays.asList(KagregFrontEnd.getModules(args2));
                        break;
                    case "-kcheck":
                        assert false : "kcheck no longer supported";
                        return;
                    case "-ktest":
                        modules.addAll(Arrays.asList(KTestFrontEnd.getModules(args2)));
                        for (KModule kModule : kModules) {
                            List<Module> ms = kModule.getKTestModules();
                            if (ms != null) {
                                modules.addAll(ms);
                            }
                        }
                        break;
                    case "-kast":
                        modules.addAll(Arrays.asList(KastFrontEnd.getModules(args2)));
                        for (KModule kModule : kModules) {
                            List<Module> ms = kModule.getKastModules();
                            if (ms != null) {
                                modules.addAll(ms);
                            }
                        }
                        break;
                    case "-krun":
                        modules.addAll(Arrays.asList(KRunFrontEnd.getModules(args2)));
                        for (KModule kModule : kModules) {
                            List<Module> ms = kModule.getKRunModules();
                            if (ms != null) {
                                modules.addAll(ms);
                            }
                        }
                        break;
                    case "-kpp":
                        modules = Arrays.asList(KppFrontEnd.getModules(args2));
                        break;
                    default:
                        invalidJarArguments();
                        return;
            }
            if (modules.size() == 0) {
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
