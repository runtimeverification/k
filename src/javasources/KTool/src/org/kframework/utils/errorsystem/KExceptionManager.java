// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.kil.ASTNode;
import org.kframework.ktest.Config.LocationData;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;
import java.util.List;

public class KExceptionManager {
    private final List<KException> exceptions = new ArrayList<KException>();

    private GlobalOptions options;

    public KExceptionManager(GlobalOptions options) {
        this.options = options;
    }

    private void printStackTrace(Throwable e) {
        if (e != null) {
            if (options.debug) {
                e.printStackTrace();
            }
        }
    }

    public void registerCriticalError(String message, Throwable e) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, e, null);
    }

    public void registerCriticalError(String message, Throwable e, LocationData location) {
        register(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, location.getSystemId(),
                location.getPosStr(), e);
    }

    public void registerInternalError(String message, Throwable e) {
        register(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, e, null);
    }

    public void registerCriticalWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, e, null);
    }

    public void registerCriticalWarning(String message, Throwable e, ASTNode node) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, e, node);
    }

    private void register(ExceptionType type, KExceptionGroup group, String message, Throwable e,
            ASTNode node) {
        if (node == null) {
            register(type, group, message, null, null, e);
        } else {
            register(type, group, message, node.getFilename(), node.getLocation(), e);
        }
    }

    private void register(ExceptionType type, KExceptionGroup group, String message,
            String filename, String location, Throwable e) {
        printStackTrace(e);
        registerInternal(new KException(type, group, message, filename, location, e));
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
        for (KException e : exceptions) {
            if (!options.warnings.includesExceptionType(e.type))
                continue;

            System.err.println(StringUtil.splitLines(e.toString()));
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
