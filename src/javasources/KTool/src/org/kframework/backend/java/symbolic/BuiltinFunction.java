// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.krun.K;
import org.kframework.krun.K.Tool;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
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

    private final String hookPropertiesFileName = "hooks.properties";

    /**
     * Set of hook module names excluded from evaluation during compilation, when each rule's
     * right-hand side and condition are partially evaluated. Certain functions, like functions
     * performing I/O operations or meta operations should only be evaluated at runtime.
     *
     * @see org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer#evaluateDefinition(org.kframework.backend.java.kil.Definition)
     * @see org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer#evaluateRule(org.kframework.backend.java.kil.Rule, org.kframework.backend.java.kil.Definition)
     */
    private final ImmutableSet<String> hookMetaModules = ImmutableSet.of(
            "#META-K",
            "MetaK",
            "Visitor",
            "#IO",
            "#FRESH",
            "Substitution");

    /**
     * Map of {@link KLabelConstant} representation of builtin (hooked) operations to
     * {@link Method} representation of Java implementation of said operations.
     */
    private Map<KLabelConstant, Method> table = new HashMap<KLabelConstant, Method>();

    public BuiltinFunction(Definition definition) {
        /* initialize {@code table} */
        String separator = System.getProperty("file.separator");
        String path = KPaths.getKBase(false) + separator + "include" + separator + "java";
        Properties properties = new Properties();

        String propertyFile = path + separator + hookPropertiesFileName;
        try {
            FileUtil.loadProperties(properties, propertyFile);
        } catch (IOException e) {
            if (definition.context().globalOptions.debug) {
                e.printStackTrace();
            }
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.INTERNAL, "Could not read from " + propertyFile));
        }

        for (String label : definition.context().labels.keySet()) {
            for (Production production : definition.context().productionsOf(label)) {
                if (production.getKLabel().equals(label) // make sure the label is a Klabel
                        && production.containsAttribute(Attribute.HOOK_KEY)) {
                    String hookAttribute = production.getAttribute(Attribute.HOOK_KEY);
                    String hookPrefix = hookAttribute.substring(0, hookAttribute.indexOf(":"));
                    /*
                     * exclude hook from evaluation during compilation if the hook is dynamic
                     * in nature (is related to I/O or to meta properties).
                     * */
                    if (K.tool() == Tool.KOMPILE && hookMetaModules.contains(hookPrefix)) {
                        continue;
                    }

                    String hook = properties.getProperty(hookAttribute);
                    if (hook == null) {
                        GlobalSettings.kem.register(new KException(
                                KException.ExceptionType.HIDDENWARNING,
                                KException.KExceptionGroup.CRITICAL, "missing entry in "
                                        + hookPropertiesFileName + " for hook " + hookAttribute,
                                production.getFilename(), production.getLocation()));
                        continue;
                    }

                    try {
                        String className = hook.substring(0, hook.lastIndexOf('.'));
                        String methodName = hook.substring(hook.lastIndexOf('.') + 1);
                        Class<?> c = Class.forName(className);
                        for (Method method : c.getDeclaredMethods()) {
                            if (method.getName().equals(methodName)) {
                                table.put(KLabelConstant.of(label, definition), method);
                                break;
                            }
                        }
                    } catch (ClassNotFoundException | SecurityException e) {
                        if (definition.context().globalOptions.debug) {
                            e.printStackTrace();
                        }
                        GlobalSettings.kem.register(new KException(
                                KException.ExceptionType.WARNING,
                                KException.KExceptionGroup.CRITICAL,
                                "missing implementation for hook " + hookAttribute + ":\n" + hook,
                                production.getFilename(), production.getLocation()));
                    }
                }
            }
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
    public Term invoke(TermContext context, KLabelConstant label, Term... arguments)
            throws IllegalAccessException, IllegalArgumentException, InvocationTargetException {
        Object[] args = Arrays.copyOf(arguments, arguments.length + 1, Object[].class);
        args[arguments.length] = context;
        // TODO(YilongL): is reflection/exception really the best way to
        // deal with builtin functions? builtin functions are supposed to be
        // super-fast...
        Method method = table.get(label);
        Term t = (Term) method.invoke(null, args);
        return t;
    }

    /**
     * Checks if the given K label represents a builtin (hooked) operation.
     * 
     * @param label
     *            the given K label
     * @return true if the given K label corresponds to a builtin operation;
     *         otherwise, false
     */
    public boolean isBuiltinKLabel(KLabelConstant label) {
        return table.containsKey(label);
    }

}
