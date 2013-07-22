package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.utils.file.KPaths;

import java.io.FileInputStream;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;


/**
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
            properties.load(new FileInputStream(path + separator + "hooks.properties"));

            for (String label : definition.context().labels.keySet()) {
                for (Production production : definition.context().productionsOf(label)) {
                    if (production.containsAttribute(Attribute.HOOK_KEY)) {
                        try {
                            String hook = properties.getProperty(
                                    production.getAttribute(Attribute.HOOK_KEY));
                            String className = hook.substring(0, hook.lastIndexOf('.'));
                            String methodName = hook.substring(hook.lastIndexOf('.') + 1);
                            Class c = Class.forName(className);
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

        /* initialize sort information in {@code SortMembership} */
        SortMembership.init(definition.context());

        /* initialize sort information in {@code MetaK} */
        MetaK.init(definition);
    }

    public static Term invoke(KLabelConstant label, Term ... arguments)
            throws IllegalAccessException, IllegalArgumentException {
        try {
            return (Term) table.get(label).invoke(null, (Object[]) arguments);
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

    public static boolean isBuiltinKLabel(KLabelConstant label) {
        return table.containsKey(label);
    }

}
