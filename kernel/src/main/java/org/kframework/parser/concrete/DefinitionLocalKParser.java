// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.kframework.utils.errorsystem.KEMException;
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
 * We get around this by expiring old classes and therefore old classloaders.
 * Note that it also does not behave correctly if a single definition is modified
 * and then parsed again. This is a future optimization
 * that can potentially be made to this class, however, what it does currently
 * is sufficient to allow a single process to be used for an entire KTest test suite,
 * which is the primary goal of this class.
 *
 * @author dwightguth
 *
 */
public class DefinitionLocalKParser {

    private static final Map<File, Class<?>> impl = new LinkedHashMap<File, Class<?>>() {
        protected boolean removeEldestEntry(Map.Entry<File,java.lang.Class<?>> eldest) {
            return size() > Runtime.getRuntime().availableProcessors() * 2;
        }
    };

    private static Class<?> resourceDomain;

    public static Class<?> init(File kompiled) {
        ClassLoader cl;
        try {
            Class<?> cached = impl.get(kompiled.getCanonicalFile());
            if (cached != null) return cached;
            cl = new URLClassLoader(new URL[] {
                    new File(JarInfo.getKBase(), "lib/java/dynamic/strategoxt.jar").toURI().toURL(),
                    new File(JarInfo.getKBase(), "lib/java/dynamic/sdf-parser.jar").toURI().toURL(),
            });
            Class<?> kparser = Class.forName("org.kframework.parser.concrete.KParser", true, cl);
            if (resourceDomain == null) resourceDomain = kparser;
            impl.put(kompiled.getCanonicalFile(), kparser);
            return kparser;
        } catch (ClassNotFoundException | IOException e) {
            throw KEMException.internalError("Failed to localize JSGLR to a thread", e);
        }
    }

    /**
     * Returns a class that has access to the resources in the sdf-parser module.
     * This method must be called after init has been called from at least one thread.
     * @return
     */
    public static Class<?> resourceDomain() {
        return resourceDomain;
    }

    private static String invokeReflective(String methodName, Class<?> kparser, Object... args) {
        try {
            List<Class<?>> classes = Arrays.asList(args).stream().map(o -> o.getClass()).collect(Collectors.toList());
            Method m = kparser.getMethod(methodName, classes.toArray(new Class<?>[classes.size()]));
            return (String) m.invoke(null, args);
        } catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException e) {
            throw KEMException.internalError("Failed to localize JSGLR to a thread", e);
        } catch (InvocationTargetException e) {
            throw new RuntimeException("JSGLR failed to parse term", e);
        }
    }

    public static String ParseKoreString(String kDefinition, File kompiled) {
        Class<?> kparser = init(kompiled);
        invokeReflective("ImportTblRule", kparser, kompiled);
        return invokeReflective("ParseKoreString", kparser, kDefinition);
    }

    public static String ParseKConfigString(String kDefinition, File kompiled) {
        Class<?> kparser = init(kompiled);
        invokeReflective("ImportTblRule", kparser, kompiled);
        return invokeReflective("ParseKConfigString", kparser, kDefinition);
    }

    public static String ParseKRuleString(String kDefinition, File kompiled) {
        Class<?> kparser = init(kompiled);
        invokeReflective("ImportTblRule", kparser, kompiled);
        return invokeReflective("ParseKRuleString", kparser, kDefinition);
    }

    /**
     * Parses a term that is subsorted to K, List, Set, Bag or Map
     *
     * @param argument
     *            The string content of the term.
     * @return The xml representation of the parsed term, or an error in the xml format.
     */
    public static String ParseKCmdString(String argument, File kompiled) {
        Class<?> kparser = init(kompiled);
        invokeReflective("ImportTblGround", kparser, kompiled);
        return invokeReflective("ParseKCmdString", kparser, argument);
    }

    public static String ParseProgramString(String program, String startSymbol, File kompiled) {
        Class<?> kparser = init(kompiled);
        invokeReflective("ImportTblPgm", kparser, kompiled);
        return invokeReflective("ParseProgramString", kparser, program, startSymbol);
    }
}
