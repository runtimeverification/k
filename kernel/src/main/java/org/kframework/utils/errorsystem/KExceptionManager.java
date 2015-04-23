// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import com.google.inject.Inject;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kore.K;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.inject.RequestScoped;

import java.lang.Thread.UncaughtExceptionHandler;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

@RequestScoped
public class KExceptionManager {
    private final List<KException> exceptions = Collections.synchronizedList(new ArrayList<>());

    private final GlobalOptions options;

    @Inject
    public KExceptionManager(GlobalOptions options) {
        this.options = options;
    }

    public void installForUncaughtExceptions() {
        Thread.setDefaultUncaughtExceptionHandler(new UncaughtExceptionHandler() {

            @Override
            public void uncaughtException(Thread t, Throwable e) {
                if (options.debug) {
                    e.printStackTrace();
                }
                exceptions.add(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL,
                        "Uncaught exception thrown of type " + e.getClass().getSimpleName()
                        + ".\nPlease rerun your program with the --debug flag to generate a stack trace, "
                        + "and file a bug report at https://github.com/kframework/k/issues", e));
                print();
            }
        });
    }

    private void printStackTrace(KException e) {
        if (e.getException() != null) {
            if (options.debug) {
                e.getException().printStackTrace();
            }
        }
    }

    public static KEMException criticalError(String message, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, node.getLocation(), node.getSource());
    }

    public static KEMException criticalError(String message, Throwable e, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, e, node.getLocation(), node.getSource());
    }

    public static KEMException criticalError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, phase, null, node.getLocation(), node.getSource());
    }

    public static KEMException internalError(String message, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, null, node.getLocation(), node.getSource());
    }

    public static KEMException internalError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, phase, null, node.getLocation(), node.getSource());
    }

    public static KEMException compilerError(String message, Throwable e, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, e, node.getLocation(), node.getSource());
    }

    public static KEMException compilerError(String message, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, null, node.getLocation(), node.getSource());
    }

    public static KEMException compilerError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, phase, null, node.getLocation(), node.getSource());
    }

    public static KEMException compilerError(String message, AbstractVisitor<?, ?, ?> phase, Throwable e, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, phase, e, node.getLocation(), node.getSource());
    }

    public static KEMException innerParserError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, phase, null, node.getLocation(), node.getSource());
    }

    public void addKException(KException kex) {
        exceptions.add(kex);
    }

    public void addAllKException(Collection<KException> kex) {
        exceptions.addAll(kex);
    }

    public void registerCompilerWarning(String message) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, null, null, null);
    }

    public void registerCompilerWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, e, null, null);
    }

    public void registerCompilerWarning(String message, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, null, node.getLocation(), node.getSource());
    }

    public void registerCompilerWarning(String message, K node) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, null, node.att().getOptional(Location.class).orElse(null), node.att().getOptional(Source.class).orElse(null));
    }

    public void registerCompilerWarning(String message, Throwable e, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, e, node.getLocation(), node.getSource());
    }

    public void registerCompilerWarning(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, phase, null, node.getLocation(), node.getSource());
    }

    public void registerCriticalWarning(String message) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, null, null, null);
    }

    public void registerCriticalWarning(String message, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, null, node.getLocation(), node.getSource());
    }

    public void registerCriticalWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, e, null, null);
    }

    public void registerCriticalWarning(String message, Throwable e, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, e, node.getLocation(), node.getSource());
    }

    public void registerInternalWarning(String message) {
        register(ExceptionType.WARNING, KExceptionGroup.INTERNAL, message, null, null, null, null);
    }

    public void registerInternalWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.INTERNAL, message, null, e, null, null);
    }

    public void registerInternalHiddenWarning(String message, Throwable e) {
        register(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, message, null, e, null, null);
    }

    public void registerInternalHiddenWarning(String message, ASTNode node) {
        register(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, message, null, null, node.getLocation(), node.getSource());
    }

    private static KEMException create(ExceptionType type, KExceptionGroup group, String message,
                                       AbstractVisitor<?, ?, ?> phase, Throwable e, Location location, Source source) {
        return new KEMException(new KException(type, group, message, phase == null ? null : phase.getName(), source, location, e));
    }

    private void register(ExceptionType type, KExceptionGroup group, String message,
                          AbstractVisitor<?, ?, ?> phase, Throwable e, Location location, Source source) {
        registerInternal(new KException(type, group, message, phase == null ? null : phase.getName(), source, location, e));
    }

    @Deprecated
    public void register(KException exception) {
        registerInternal(exception);
    }

    private void registerInternal(KException exception) {
        if (!options.warnings.includesExceptionType(exception.type))
            return;
        exceptions.add(exception);
        if (exception.type == ExceptionType.ERROR || options.warnings2errors) {
            throw new KEMException(exception);
        }
    }

    public void print() {
        Collections.sort(exceptions, new Comparator<KException>() {
            @Override
            public int compare(KException arg0, KException arg1) {
                return arg0.toString(options.verbose).compareTo(arg1.toString(options.verbose));
            }
        });
        KException last = null;
        for (KException e : exceptions) {
            if (last != null && last.toString(options.verbose).equals(e.toString(options.verbose))) {
                continue;
            }
            printStackTrace(e);
            System.err.println(StringUtil.splitLines(e.toString(options.verbose)));
            last = e;
        }
    }

    public void registerThrown(KEMException e) {
        exceptions.add(e.exception);
    }

    public List<KException> getExceptions() {
        return exceptions;
    }
}
