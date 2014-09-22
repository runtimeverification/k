// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.ServiceLoader;

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

public class Main {

    /**
     * @param args
     *            - the running arguments for the K3 tool. First argument must be one of the following: kompile|kast|krun.
     * @throws IOException when loadDefinition fails
     */
    public static void main(String[] args) {
        AnsiConsole.systemInstall();

        if (args.length >= 1) {

            Injector injector = getInjector(args);
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

    public static Injector getInjector(String[] args) {
        ServiceLoader<KModule> kLoader = ServiceLoader.load(KModule.class);
        List<KModule> kModules = new ArrayList<>();
        for (KModule m : kLoader) {
            kModules.add(m);
        }

        List<Module> modules = new ArrayList<>();

        String[] args2 = Arrays.copyOfRange(args, 1, args.length);
            switch (args[0]) {
                case "-kompile":
                    modules.addAll(KompileFrontEnd.getModules(args2));
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKompileModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kagreg":
                    modules = KagregFrontEnd.getModules(args2);
                    break;
                case "-kcheck":
                    throw new AssertionError("kcheck no longer supported");
                case "-ktest":
                    modules.addAll(KTestFrontEnd.getModules(args2));
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKTestModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kast":
                    modules.addAll(KastFrontEnd.getModules(args2));
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKastModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-krun":
                    List<Module> definitionSpecificModules = new ArrayList<>();
                    definitionSpecificModules.addAll(KRunFrontEnd.getDefinitionSpecificModules(args2));
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getDefinitionSpecificKRunModules();
                        if (ms != null) {
                            definitionSpecificModules.addAll(ms);
                        }
                    }

                    modules.addAll(KRunFrontEnd.getModules(args2, definitionSpecificModules));
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKRunModules(definitionSpecificModules);
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kpp":
                    modules = KppFrontEnd.getModules(args2);
                    break;
                default:
                    invalidJarArguments();
                    throw new AssertionError("unreachable");
        }
        if (modules.size() == 0) {
            //boot error, we should have printed it already
            System.exit(1);
        }
        Injector injector = Guice.createInjector(modules);
        return injector;
    }

    private static void invalidJarArguments() {
        System.err.println("The first argument of K3 not recognized. Try -kompile, -kast, -krun, -ktest, or -kpp.");
        System.exit(1);
    }
}
