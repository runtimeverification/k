package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.krun.K;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import com.google.common.collect.ImmutableSet;


/**
 * Utility class that handles the builtin (hooked) operations and their Java
 * implementations.
 * 
 * @author AndreiS
 */
public class BuiltinFunction {

    private static final String hookPropertiesFileName = "hooks.properties";

    /**
     * Set of hook module names excluded from evaluation during compilation.
     */
    private static final ImmutableSet hookMetaModules = ImmutableSet.of(
            "#META-K",
            "MetaK",
            "Visitor",
            "#IO");

    /**
     * Map of {@link KLabelConstant} representation of builtin (hooked) operations to
     * {@link Method} representation of Java implementation of said operations.
     */
    private static final Map<KLabelConstant, Method> table = new HashMap<KLabelConstant, Method>();

    public static void init(Definition definition) {
        /* initialize {@code table} */
        try {
            String separator = System.getProperty("file.separator");
            String path = KPaths.getKBase(false) + separator + "include" + separator + "java";
            Properties properties = new Properties();

            FileUtil.loadProperties(properties, path + separator + hookPropertiesFileName);

            for (String label : definition.context().labels.keySet()) {
                for (Production production : definition.context().productionsOf(label)) {
                    if (production.getKLabel().equals(label)    // make sure the label is a Klabel
                            && production.containsAttribute(Attribute.HOOK_KEY)) {
                        String hookAttribute = production.getAttribute(Attribute.HOOK_KEY);
                        String hookPrefix = hookAttribute.substring(0, hookAttribute.indexOf(":"));
                        /*
                         * exclude hook from evaluation during compilation if the hook is dynamic
                         * in nature (is related to I/O or to meta properties).
                         * */
                        if (K.do_kompilation && hookMetaModules.contains(hookPrefix)) {
                            continue;
                        }

                        String hook = properties.getProperty(hookAttribute);
                        if (hook == null) {
                            GlobalSettings.kem.register(new KException(
                                    KException.ExceptionType.HIDDENWARNING,
                                    KException.KExceptionGroup.CRITICAL,
                                    "missing entry in " + hookPropertiesFileName
                                            + " for hook " + hookAttribute,
                                    production.getFilename(),
                                    production.getLocation()));
                            continue;
                        }

                        try {
                            String className = hook.substring(0, hook.lastIndexOf('.'));
                            String methodName = hook.substring(hook.lastIndexOf('.') + 1);
                            Class<?> c = Class.forName(className);
                            for (Method method : c.getDeclaredMethods()) {
                                if (method.getName().equals(methodName)) {
                                    table.put(
                                            KLabelConstant.of(label, definition.context()),
                                            method);
                                    break;
                                }
                            }
                        } catch (Exception e) {
                            GlobalSettings.kem.register(new KException(
                                    KException.ExceptionType.WARNING,
                                    KException.KExceptionGroup.CRITICAL,
                                    "missing implementation for hook " + hookAttribute + ":\n"
                                            + hook,
                                    production.getFilename(),
                                    production.getLocation()));
                        }
                    }
                }
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Invokes the Java implementation of a builtin (hooked) operation.
     * 
     * @param context
     *            the {@code TermContext}
     * @param label
     *            the corresponding K label of the builtin operation
     * @param arguments
     *            the arguments of the builtin operation
     * @return the result of the builtin operation if the evaluation succeeds
     * @throws IllegalAccessException
     * @throws IllegalArgumentException
     */
    public static Term invoke(TermContext context, KLabelConstant label, Term ... arguments)
            throws IllegalAccessException, IllegalArgumentException {
        Object[] args =  Arrays.copyOf(arguments, arguments.length + 1, Object[].class);
        args[arguments.length] =  context;
        try {
            // TODO(YilongL): is reflection/exception really the best way to
            // deal with builtin functions? builtin functions are supposed to be
            // super-fast...
            Method method = table.get(label);
            Term t = (Term) method.invoke(null, args);
            return t;
        } catch (InvocationTargetException e) {
            Throwable t = e.getTargetException();
            if (t instanceof Error) {
                throw (Error)t;
            }
            if (t instanceof RuntimeException) {
                throw (RuntimeException)t;
            }
            assert false : "Builtin functions should not throw checked exceptions";
            return null; //unreachable
        }
    }

    /**
     * Checks if the given K label represents a builtin (hooked) operation.
     * 
     * @param label
     *            the given K label
     * @return true if the given K label corresponds to a builtin operation;
     *         otherwise, false
     */
    public static boolean isBuiltinKLabel(KLabelConstant label) {
        return table.containsKey(label);
    }

}
