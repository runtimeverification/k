// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.JarInfo;

/**
 * Abstracts the JSGLR dependency out from the classpath of the K core.
 * By doing this, we are able to instantiate a new classloader with access
 * to the third-party code, and create a new version of the static state intrinsic
 * to JSGLR for every definition we execute. This means that multiple definitions
 * can be parsed in different threads within the same process.
 *
 * Note that a consequence of this is that if you use many definitions in
 * the same process, you will use up a lot of memory dedicated to the JVM code cache.
 * Currently the implementation of this class does not expire classloaders
 * when too many of them have been instantiated. It also does not behave correctly
 * if a single definition is modified and then parsed again. These are future optimizations
 * that can potentially be made to this class, however, what it does currently
 * is sufficient to allow a single process to be used for an entire KTest test suite,
 * which is the primary goal of this class.
 *
 * @author dwightguth
 *
 */
public class DefinitionLocalKParser {

    private static final Map<File, Class<?>> impl = new HashMap<>();

    public static void init(File kompiled) {
        ClassLoader cl;
        try {
            if (impl.containsKey(kompiled.getCanonicalFile())) return;
            cl = new URLClassLoader(new URL[] {
                    new File(JarInfo.getKBase(false), "lib/java/dynamic/strategoxt.jar").toURI().toURL(),
                    new File(JarInfo.getKBase(false), "lib/java/dynamic/sdf-parser.jar").toURI().toURL()
            });
            Class<?> kparser = Class.forName("org.kframework.parser.concrete.KParser", true, cl);
            impl.put(kompiled.getCanonicalFile(), kparser);
        } catch (ClassNotFoundException | IOException e) {
            throw KExceptionManager.internalError("Failed to localize JSGLR to a thread", e);
        }
    }

    /**
     * Returns a class that has access to the resources in the sdf-parser module.
     * This method must be called after init has been called from at least one thread.
     * @return
     */
    public static Class<?> resourceDomain() {
        Iterator<Class<?>> i = impl.values().iterator();
        assert i.hasNext();
        return i.next();
    }

    private static String invokeReflective(String methodName, File kompiled, Object... args) {
        try {
            List<Class<?>> classes = Arrays.asList(args).stream().map(o -> o.getClass()).collect(Collectors.toList());
            Method m = impl.get(kompiled.getCanonicalFile()).getMethod(methodName, classes.toArray(new Class<?>[classes.size()]));
            return (String) m.invoke(null, args);
        } catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException | InvocationTargetException | IOException e) {
            throw KExceptionManager.internalError("Failed to localize JSGLR to a thread", e);
        }
    }

    public static String ParseKoreString(String kDefinition, File kompiled) {
        init(kompiled);
        invokeReflective("ImportTblRule", kompiled, kompiled);
        return invokeReflective("ParseKoreString", kompiled, kDefinition);
    }

    public static String ParseKConfigString(String kDefinition, File kompiled) {
        init(kompiled);
        invokeReflective("ImportTblRule", kompiled, kompiled);
        return invokeReflective("ParseKConfigString", kompiled, kDefinition);
    }

    public static String ParseKRuleString(String kDefinition, File kompiled) {
        init(kompiled);
        invokeReflective("ImportTblRule", kompiled, kompiled);
        return invokeReflective("ParseKRuleString", kompiled, kDefinition);
    }

    /**
     * Parses a term that is subsorted to K, List, Set, Bag or Map
     *
     * @param argument
     *            The string content of the term.
     * @return The xml representation of the parsed term, or an error in the xml format.
     */
    public static String ParseKCmdString(String argument, File kompiled) {
        init(kompiled);
        invokeReflective("ImportTblGround", kompiled, kompiled);
        return invokeReflective("ParseKCmdString", kompiled, argument);
    }

    public static String ParseProgramString(String program, String startSymbol, File kompiled) {
        init(kompiled);
        invokeReflective("ImportTblPgm", kompiled, kompiled);
        return invokeReflective("ParseProgramString", kompiled, program, startSymbol);
    }
}
