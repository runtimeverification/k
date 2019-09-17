// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.attributes.HasLocation;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

/**
 * Thrown to indicate that the K Exception manager has terminated the application due to an error.
 *
 * @author dwightguth
 */
public class KEMException extends RuntimeException {
    public static final int TERMINATED_WITH_ERRORS_EXIT_CODE = 113;

    public final KException exception;

    KEMException(KException e) {
        super(e.toString(), e.getException());
        this.exception = e;
    }

    KEMException(KException e, ExceptionType type) {
        super(e.toString(), e.getException());
        this.exception = new KException(type, e.exceptionGroup, e.getMessage(), e.getSource(), e.getLocation(), e.getException());
    }

    public static KEMException debuggerError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.DEBUGGER, message, null, null, null);
    }

    public static KEMException criticalError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, null);
    }

    public static KEMException criticalError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, e, null, null);
    }

    public static KEMException criticalError(String message, HasLocation node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public static KEMException criticalError(String message, Throwable e, HasLocation node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, e, node.location().orElse(null), node.source().orElse(null));
    }


    public static KEMException criticalError(String message, Throwable e, Location loc, Source source) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, e, loc, source);
    }

    public static KEMException internalError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, null, null);
    }

    public static KEMException internalError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, e, null, null);
    }

    public static KEMException internalError(String message, HasLocation node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public static KEMException compilerError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, null, null);
    }

    public static KEMException compilerError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, e, null, null);
    }

    public static KEMException compilerError(String message, HasLocation node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public static KEMException compilerError(String message, Throwable e, HasLocation node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, e, node.location().orElse(null), node.source().orElse(null));
    }

    public static KEMException innerParserError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, null, null, null);
    }

    public static KEMException innerParserError(String message, Throwable e, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, e, location, source);
    }

    public static KEMException outerParserError(String message, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.OUTER_PARSER, message, null, location, source);
    }

    public static KEMException outerParserError(String message, Throwable e, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.OUTER_PARSER, message, e, location, source);
    }

    public static KEMException asError(KEMException warning) {
        return new KEMException(warning.exception, ExceptionType.ERROR);
    }

    @Override
    public String getMessage() {
        return exception.toString();
    }

    private static KEMException create(ExceptionType type, KExceptionGroup group, String message,
                                       Throwable e, Location location, Source source) {
        return new KEMException(new KException(type, group, message, source, location, e));
    }
}
