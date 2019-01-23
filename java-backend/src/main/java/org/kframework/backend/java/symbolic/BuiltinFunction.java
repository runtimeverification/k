// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.attributes.Att;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.ImpureFunctionException;
import org.kframework.kil.Attribute;
import org.kframework.kore.KLabel;
import org.kframework.kore.KORE;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

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
    private final Map<KLabelConstant, MethodHandle> table = new HashMap<>();


    /**
     * Constructs a builtin function table mapping KLabels to the methods that implement their builtin
     * functions.
     *
     * The "impure" attribute on productions is used to exclude functions from evaluation during compilation,
     * when each rule's right-hand side and condition are partially evaluated. Certain functions, like functions
     * performing I/O operations or meta operations should only be evaluated at runtime.
     */
    public BuiltinFunction(Definition definition, Map<String, MethodHandle> hookProvider, KExceptionManager kem, Stage stage) {
        MethodHandles.Lookup lookup = MethodHandles.lookup();
        MethodType hookType = MethodType.methodType(Term.class, Object[].class);
        MethodHandle throwImpureExceptionHandle;
        try {
            throwImpureExceptionHandle = lookup.findStatic(BuiltinFunction.class,
                    "throwImpureException", hookType);
        } catch (NoSuchMethodException | IllegalAccessException e) {
            throw KEMException.internalError("Failed to load partial evaluation hook implementation", e);
        }
        for (Map.Entry<String, Att> entry : definition.kLabelAttributes().entrySet()) {
            String hookAttribute = entry.getValue().getOptional(Attribute.HOOK_KEY).orElse(null);
            if (hookAttribute != null) {
                /*
                 * exclude hook from evaluation during compilation if the hook is dynamic
                 * in nature (is related to I/O or to meta properties).
                 * */
                // TODO(KORE): removed check to allow the rewrite engine to execute impure functions when the Stage flag is incorrectly set.
                // this allows impure function to execute statically so we need to figure out an alternate solution soon.
//                if (stage == Stage.INITIALIZING && entry.getValue().getAttr(Attribute.IMPURE_KEY) != null) {
//                    table.put(KLabelConstant.of(entry.getKey(), definition), throwImpureExceptionHandle);
//                    continue;
//                }

                if (!hookProvider.containsKey(hookAttribute)) {
                    kem.registerCriticalHiddenWarning("missing entry for hook " + hookAttribute);
                    continue;
                }

                table.put(KLabelConstant.of(KORE.KLabel(entry.getKey()), definition), hookProvider.get(hookAttribute));
            }
        }
    }

    private static Term throwImpureException(Object... args) {
        throw new ImpureFunctionException();
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
    // DISABLE EXCEPTION CHECKSTYLE
    public Term invoke(TermContext context, KLabelConstant label, Term... arguments)
            throws Throwable {
    // ENABLE EXCEPTION CHECKSTYLE
        Object[] args = Arrays.copyOf(arguments, arguments.length + 1, Object[].class);
        args[arguments.length] = context;
        // TODO(YilongL): is reflection/exception really the best way to
        // deal with builtin functions? builtin functions are supposed to be
        // super-fast...
        return (Term) table.get(label).invokeWithArguments(args);
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
