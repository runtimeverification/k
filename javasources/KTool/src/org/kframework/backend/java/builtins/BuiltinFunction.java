package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.utils.file.KPaths;

import java.io.FileInputStream;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

/**
 * @author: AndreiS
 */
public class BuiltinFunction {

    private static final Map<KLabelConstant, Method> table = new HashMap<KLabelConstant, Method>();

    public static void add(
            KLabelConstant label,
            String className,
            String methodName,
            String ... typeNames) {
        try {
            Class[] types = new Class[typeNames.length];
            for (int i = 0; i < typeNames.length; ++i) {
                types[i] = Class.forName(typeNames[i]);
            }
            table.put(label, Class.forName(className).getDeclaredMethod(methodName, types));
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        }
    }

    public static void init(Context context) {
        try {
            String separator = System.getProperty("file.separator");
            String path = KPaths.getKBase(false) + separator + "include" + separator + "java";
            Properties properties = new Properties();
            properties.load(new FileInputStream(path + separator + "hooks.properties"));

            for (String label : context.labels.keySet()) {
                for (Production production : context.productionsOf(label)) {
                    if (production.containsAttribute(Attribute.HOOK_KEY)) {
                        if (properties.containsKey(production.getAttribute(Attribute.HOOK_KEY))) {
                            // TODO(AndreiS): finish hook initializer
                            //add(
                            //    KLabelConstant.of(label, context),
                            //    properties.get(production.getAttribute(Attribute.HOOK_KEY)));
                        } else {

                        }
                    }
                }
            }

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static KItem invoke(KLabelConstant label, Term ... arguments)
            throws IllegalArgumentException, InvocationTargetException {
        try {
            return (KItem) table.get(label).invoke(null, arguments);
        } catch (IllegalAccessException e) {
            /* unreachable code */
            e.printStackTrace();
            return null;
        }
    }

}
