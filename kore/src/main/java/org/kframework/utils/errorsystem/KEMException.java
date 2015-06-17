// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.parser.ProductionReference;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

/**
 * Thrown to indicate that the K Exception manager has terminated the application due to an error.
 *
 * @author dwightguth
 */
public class KEMException extends RuntimeException {
    public final KException exception;

    KEMException(KException e) {
        super(e.toString(), e.getException());
        this.exception = e;
    }

    public static KEMException criticalError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, null, null);
    }

    public static KEMException criticalError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, e, null, null);
    }

    public static KEMException criticalError(String message, ProductionReference node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public static KEMException criticalError(String message, Sentence node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, node.att().getOptional(Location.class).orElse(null), node.att().getOptional(Source.class).orElse(null));
    }

    public static KEMException criticalError(String message, K node) {
        return create(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message, null, node.att().getOptional(Location.class).orElse(null), node.att().getOptional(Source.class).orElse(null));
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

    public static KEMException internalError(String message, K node) {
        return create(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, null, node.att().getOptional(Location.class).orElse(null), node.att().getOptional(Source.class).orElse(null));
    }

    public static KEMException compilerError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, null, null);
    }

    public static KEMException compilerError(String message, Throwable e) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, e, null, null);
    }

    public static KEMException compilerError(String message, K node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, node.att().getOptional(Location.class).orElse(null), node.att().getOptional(Source.class).orElse(null));
    }

    public static KEMException compilerError(String message, Sentence node) {
        return create(ExceptionType.ERROR, KExceptionGroup.COMPILER, message, null, node.att().getOptional("Location", Location.class).orElse(null), node.att().getOptional("Source", Source.class).orElse(null));
    }

    public static KEMException innerParserError(String message) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, null, null, null);
    }

    public static KEMException innerParserError(String message, Throwable e, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, e, location, source);
    }

    public static KEMException outerParserError(String message, Throwable e, Source source, Location location) {
        return create(ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, message, e, location, source);
    }

    @Override
    public String getMessage() {
        return exception.toString();
    }

    private static KEMException create(ExceptionType type, KExceptionGroup group, String message,
                                       Throwable e, Location location, Source source) {
        return new KEMException(new KException(type, group, message, null, source, location, e));
    }
}
