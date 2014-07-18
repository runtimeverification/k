// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Builtins;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

import com.google.common.collect.ImmutableSet;
import com.google.inject.Inject;
import com.google.inject.Provider;

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

    private final Map<Class<?>, Provider<Object>> builtinFunctionProviders;

    /**
     *
     * @param definition
     * @param injector
     */
    @Inject
    public BuiltinFunction(Context context, @Builtins Map<Class<?>, Provider<Object>> builtinFunctionProviders, KExceptionManager kem, Tool tool) {
        this.builtinFunctionProviders = builtinFunctionProviders;
        /* initialize {@code table} */
        Properties properties = new Properties();

        try {
            FileUtil.loadProperties(properties, getClass(), hookPropertiesFileName);
        } catch (IOException e) {
            kem.registerInternalError("Could not read from resource " + hookPropertiesFileName, e);
        }

        for (String label : context.klabels.keySet()) {
            for (Production production : context.productionsOf(label)) {
                if (production.getKLabel().equals(label) // make sure the label is a Klabel
                        && production.containsAttribute(Attribute.HOOK_KEY)) {
                    String hookAttribute = production.getAttribute(Attribute.HOOK_KEY);
                    String hookPrefix = hookAttribute.substring(0, hookAttribute.indexOf(":"));
                    /*
                     * exclude hook from evaluation during compilation if the hook is dynamic
                     * in nature (is related to I/O or to meta properties).
                     * */
                    if (tool == Tool.KOMPILE && hookMetaModules.contains(hookPrefix)) {
                        continue;
                    }

                    String hook = properties.getProperty(hookAttribute);
                    if (hook == null) {
                        kem.register(new KException(
                                KException.ExceptionType.HIDDENWARNING,
                                KException.KExceptionGroup.CRITICAL, "missing entry in "
                                        + hookPropertiesFileName + " for hook " + hookAttribute,
                                production.getSource(), production.getLocation()));
                        continue;
                    }

                    try {
                        String className = hook.substring(0, hook.lastIndexOf('.'));
                        String methodName = hook.substring(hook.lastIndexOf('.') + 1);
                        Class<?> c = Class.forName(className);
                        for (Method method : c.getDeclaredMethods()) {
                            if (method.getName().equals(methodName)) {
                                table.put(KLabelConstant.of(label, context), method);
                                break;
                            }
                        }
                    } catch (ClassNotFoundException | SecurityException e) {
                        kem.registerCriticalWarning("missing implementation for hook "
                                + hookAttribute + ":\n" + hook, e, production);
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
        Term t = (Term) method.invoke(builtinFunctionProviders.get(method.getDeclaringClass()).get(), args);
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
