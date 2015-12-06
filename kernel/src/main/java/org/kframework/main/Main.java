// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.main;

import com.google.inject.Guice;
import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.Module;
import com.google.inject.Provider;
import com.google.inject.ProvisionException;
import com.google.inject.TypeLiteral;
import com.google.inject.name.Named;
import com.google.inject.spi.Message;
import com.martiansoftware.nailgun.NGContext;
import org.fusesource.jansi.AnsiConsole;
import org.kframework.kast.KastFrontEnd;
import org.kframework.kdep.KDepFrontEnd;
import org.kframework.kdoc.KDocFrontEnd;
import org.kframework.kompile.KompileFrontEnd;
import org.kframework.krun.KRunFrontEnd;
import org.kframework.kserver.KServerFrontEnd;
import org.kframework.ktest.KTestFrontEnd;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.WorkingDir;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.SimpleScope;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.ServiceLoader;

public class Main {

    /**
     * @param args
     *            - the running arguments for the K3 tool. First argument must be one of the following: kompile|kast|krun.
     * @throws IOException when loadDefinition fails
     */
    public static void main(String[] args) {
        isNailgun = false;
        AnsiConsole.systemInstall();
        if (args.length >= 1) {

            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
            Injector injector = getInjector(args[0]);
            int result = injector.getInstance(Main.class).runApplication(args[0], args2, new File("."), System.getenv());
            AnsiConsole.systemUninstall();
            System.exit(result);
        }
        AnsiConsole.systemUninstall();
        invalidJarArguments();
    }

    private static volatile boolean isNailgun;

    public static boolean isNailgun() {
        return isNailgun;
    }

    public static void nailMain(NGContext context) {
        isNailgun = true;
        if (context.getArgs().length >= 1) {
            String[] args2 = Arrays.copyOfRange(context.getArgs(), 1, context.getArgs().length);
            KServerFrontEnd kserver = KServerFrontEnd.instance();
            int result = kserver.run(context.getArgs()[0], args2, new File(context.getWorkingDirectory()), (Map) context.getEnv());
            System.exit(result);
            return;
        }
        invalidJarArguments();
    }

    private final Provider<KExceptionManager> kem;
    private final Provider<FrontEnd> frontEnd;
    private final SimpleScope requestScope;

    @Inject
    public Main(
            Provider<KExceptionManager> kem,
            Provider<FrontEnd> frontEnd,
            @Named("requestScope") SimpleScope requestScope) {
        this.kem = kem;
        this.frontEnd = frontEnd;
        this.requestScope = requestScope;
    }

    public SimpleScope getRequestScope() {
        return requestScope;
    }

    public int runApplication(String tool, String[] args, File workingDir, Map<String, String> env) {
        try {
            requestScope.enter();
            seedInjector(requestScope, tool, args, workingDir, env);
            return runApplication();
        } finally {
            requestScope.exit();
        }
    }

    public int runApplication() {
        KExceptionManager kem = this.kem.get();
        kem.installForUncaughtExceptions();
        try {
            int retval = frontEnd.get().main();
            return retval;
        } catch (ProvisionException e) {
            for (Message m : e.getErrorMessages()) {
                if (!(m.getCause() instanceof KEMException)) {
                    throw e;
                } else {
                    KEMException ex = (KEMException) m.getCause();
                    kem.registerThrown(ex);
                }
            }
            kem.print();
            return 1;
        }
    }

    public static void seedInjector(SimpleScope scope, String tool, String[] args, File workingDir,
            Map<String, String> env) {
        scope.seed(Key.get(File.class, WorkingDir.class), workingDir);
        scope.seed(Key.get(new TypeLiteral<Map<String, String>>() {}, Environment.class), env);
        scope.seed(Key.get(String[].class, Options.class), args);
    }

    public static Injector getInjector(String tool) {
        ServiceLoader<KModule> kLoader = ServiceLoader.load(KModule.class);
        List<KModule> kModules = new ArrayList<>();
        for (KModule m : kLoader) {
            kModules.add(m);
        }

        List<Module> modules = new ArrayList<>();

            switch (tool) {
                case "-kserver":
                    modules.addAll(KServerFrontEnd.getModules());
                    break;
                case "-kompile":
                    modules.addAll(KompileFrontEnd.getModules());
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKompileModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-ktest":
                    modules.addAll(KTestFrontEnd.getModules());
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKTestModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kdoc":
                    modules.addAll(KDocFrontEnd.getModules());
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKDocModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kast":
                    modules.addAll(KastFrontEnd.getModules());
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKastModules();
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kdep":
                    modules = KDepFrontEnd.getModules();
                    break;
                case "-krun":
                    List<Module> definitionSpecificModules = new ArrayList<>();
                    definitionSpecificModules.addAll(KRunFrontEnd.getDefinitionSpecificModules());
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getDefinitionSpecificKRunModules();
                        if (ms != null) {
                            definitionSpecificModules.addAll(ms);
                        }
                    }

                    modules.addAll(KRunFrontEnd.getModules(definitionSpecificModules));
                    for (KModule kModule : kModules) {
                        List<Module> ms = kModule.getKRunModules(definitionSpecificModules);
                        if (ms != null) {
                            modules.addAll(ms);
                        }
                    }
                    break;
                case "-kpp":
                    modules = KppFrontEnd.getModules();
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
        System.err.println("The first argument of K3 not recognized. Try -kompile, -kast, -krun, -ktest, -kserver, or -kpp.");
        System.exit(1);
    }
}
