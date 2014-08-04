// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.ktest.Config.LocationData;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import com.google.inject.Inject;
import com.google.inject.Singleton;

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

    private void printStackTrace(Throwable e) {
        if (e != null) {
            if (options.debug) {
                e.printStackTrace();
            }
        }
    }

    public void registerCriticalError(String message) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, null);
    }

    public void registerCriticalError(String message, ASTNode node) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, node);
    }

    public void registerCriticalError(String message, Throwable e) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, e, null);
    }

    public void registerCriticalError(String message, Throwable e, ASTNode node) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, e, node);
    }

    public void registerCriticalError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, phase, null, node);
    }

    public void registerCriticalError(String message, Throwable e, LocationData location) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, location.getSystemId(),
                location.getPosStr(), e);
    }

    public void registerInternalError(String message, Throwable e) {
        register(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, e, null);
    }

    public void registerInternalError(String message, AbstractVisitor<?, ?, ?> phase, ASTNode node) {
        register(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, phase, null, node);
    }

    public void registerCriticalWarning(String message, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, null, node);
    }

    public void registerCriticalWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, e, null);
    }

    public void registerCriticalWarning(String message, Throwable e, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, e, node);
    }

    private void register(ExceptionType type, KExceptionGroup group, String message, AbstractVisitor<?, ?, ?> phase, Throwable e,
            ASTNode node) {
        if (node == null) {
            register(type, group, message, phase, null, null, e);
        } else {
            register(type, group, message, phase, node.getFilename(), node.getLocation(), e);
        }
    }

    private void register(ExceptionType type, KExceptionGroup group, String message,
            AbstractVisitor<?, ?, ?> phase, String filename, String location, Throwable e) {
        printStackTrace(e);
        registerInternal(new KException(type, group, message, phase == null ? null : phase.getName(), filename, location, e));
    }

    @Deprecated
    public void register(KException exception) {
        registerInternal(exception);
    }

    private void registerInternal(KException exception) {
        exceptions.add(exception);
        if (exception.type == ExceptionType.ERROR) {
            throw new KEMException(exception);
        }
    }

    public void print() {
        Collections.sort(exceptions, new Comparator<KException>() {
            @Override
            public int compare(KException arg0, KException arg1) {
                return arg0.toString().compareTo(arg1.toString());
            }
        });
        KException last = null;
        for (KException e : exceptions) {
            if (!options.warnings.includesExceptionType(e.type))
                continue;

            if (last != null && last.toString().equals(e.toString())) {
                continue;
            }
            System.err.println(StringUtil.splitLines(e.toString()));
            last = e;
        }
    }

    /**
     * Thrown to indicate that the K Exception manager has terminated the application due to an error.
     * @author dwightguth
     */
    public static class KEMException extends RuntimeException {
        public final KException exception;
        private KEMException(KException e) {
            super(e.getException());
            this.exception = e;
        }
    }

    public List<KException> getExceptions() {
        return exceptions;
    }
}
