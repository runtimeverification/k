// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.Location;
import org.kframework.kil.Source;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import com.google.inject.Inject;
import com.google.inject.Singleton;

import java.lang.Thread.UncaughtExceptionHandler;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

@Singleton
public class KExceptionManager {
    private final List<KException> exceptions = new ArrayList<KException>();

    private final GlobalOptions options;

    @Inject
    KExceptionManager(GlobalOptions options) {
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
                        + ".\nPlease file a bug report at https://github.com/kframework/k/issues", e));
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

    public static KEMException criticalError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, null, null);
    }

    public static KEMException criticalError(String message, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, node.getLocation(), node.getSource());
    }

    public static KEMException criticalError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, e, null, null);
    }

    public static KEMException criticalError(String message, Throwable e, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, e, node.getLocation(), node.getSource());
    }

    public static KEMException criticalError(String message, Throwable e, Location loc, Source source) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, e, loc, source);
    }


    public static KEMException criticalError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, phase, null, node.getLocation(), node.getSource());
    }

    public static KEMException internalError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, null, null, null);
    }

    public static KEMException internalError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, e, null, null);
    }

    public static KEMException internalError(String message, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, null, node.getLocation(), node.getSource());
    }

    public static KEMException internalError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, phase, null, node.getLocation(), node.getSource());
    }

    public static KEMException compilerError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, null, null, null);
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

    public static KEMException innerParserError(String message, Throwable e, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, null, e, location, source);
    }

    public static KEMException outerParserError(String message, Throwable e, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, null, e, location, source);
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
        synchronized(exceptions) {
            exceptions.add(exception);
            if (exception.type == ExceptionType.ERROR) {
                throw new KEMException(exception);
            }
        }
    }

    public void print() {
        synchronized(exceptions) {
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
    }

    /**
     * Thrown to indicate that the K Exception manager has terminated the application due to an error.
     * @author dwightguth
     */
    public static class KEMException extends RuntimeException {
        public final KException exception;
        KEMException(KException e) {
            super(e.toString(), e.getException());
            this.exception = e;
        }

        @Override
        public String getMessage() {
            return exception.toString();
        }

        public void register(KExceptionManager kem) {
            synchronized(kem.getExceptions()) {
                kem.getExceptions().add(exception);
            }
        }
    }

    public List<KException> getExceptions() {
        return exceptions;
    }
}
