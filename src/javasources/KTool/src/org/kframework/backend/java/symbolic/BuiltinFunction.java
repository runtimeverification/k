package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.krun.K;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;


/**
 * Utility class that handles the builtin (hooked) operations and their Java
 * implementations.
 * 
 * @author AndreiS
 */
public class BuiltinFunction {

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
            FileUtil.loadProperties(properties, path + separator + "hooks.properties");

            for (String label : definition.context().labels.keySet()) {
                for (Production production : definition.context().productionsOf(label)) {
                    if (production.containsAttribute(Attribute.HOOK_KEY)) {
                        try {
                            String hook = properties.getProperty(
                                    production.getAttribute(Attribute.HOOK_KEY));
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
                            // TODO(AndreiS): report errors
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
            /* do not evaluate meta functions during the compilation */
            if (K.do_kompilation && method.getDeclaringClass().getSimpleName().equals("MetaK")) {
                return null;
            }

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
