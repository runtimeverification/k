// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.ImpureFunctionException;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Builtins;
import org.kframework.utils.inject.RequestScoped;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.MethodType;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import com.google.inject.Inject;
import com.google.inject.Provider;

/**
 * Utility class that handles the builtin (hooked) operations and their Java
 * implementations.
 *
 * @author AndreiS
 */
@RequestScoped
public class BuiltinFunction {

    /**
     * Map of {@link KLabelConstant} representation of builtin (hooked) operations to
     * {@link Method} representation of Java implementation of said operations.
     */
    private Map<KLabelConstant, MethodHandle> table = new HashMap<>();


    /**
     * Constructs a builtin function table mapping KLabels to the methods that implement their builtin
     * functions.
     *
     * The "impure" attribute on productions is used to exclude functions from evaluation during compilation,
     * when each rule's right-hand side and condition are partially evaluated. Certain functions, like functions
     * performing I/O operations or meta operations should only be evaluated at runtime.
     *
     * @see org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer#evaluateDefinition(org.kframework.backend.java.kil.Definition)
     * @see org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer#evaluateRule(org.kframework.backend.java.kil.Rule, org.kframework.backend.java.kil.Definition)
     */
    @Inject
    public BuiltinFunction(Definition definition, @Builtins Map<String, Provider<MethodHandle>> hookProvider, KExceptionManager kem, Stage stage) {
        MethodHandles.Lookup lookup = MethodHandles.lookup();
        MethodType hookType = MethodType.methodType(Term.class, Object[].class);
        MethodHandle throwImpureExceptionHandle;
        try {
            throwImpureExceptionHandle = lookup.findStatic(BuiltinFunction.class,
                    "throwImpureException", hookType);
        } catch (NoSuchMethodException | IllegalAccessException e) {
            throw KEMException.internalError("Failed to load partial evaluation hook implementation", e);
        }
        for (Map.Entry<String, Attributes> entry : definition.kLabelAttributes().entrySet()) {
            String hookAttribute = entry.getValue().getAttr(Attribute.HOOK_KEY);
            if (hookAttribute != null) {
                /*
                 * exclude hook from evaluation during compilation if the hook is dynamic
                 * in nature (is related to I/O or to meta properties).
                 * */
                if (stage == Stage.INITIALIZING && entry.getValue().getAttr(Attribute.IMPURE_KEY) != null) {
                    table.put(KLabelConstant.of(entry.getKey(), definition), throwImpureExceptionHandle);
                    continue;
                }

                if (!hookProvider.containsKey(hookAttribute)) {
                    kem.register(new KException(
                            KException.ExceptionType.HIDDENWARNING,
                            KException.KExceptionGroup.CRITICAL, "missing entry for hook " + hookAttribute));
                    continue;
                }

                table.put(KLabelConstant.of(entry.getKey(), definition), hookProvider.get(hookAttribute).get());
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
        Term t = (Term) table.get(label).invokeWithArguments(args);
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
