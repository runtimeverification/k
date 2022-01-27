// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import com.google.inject.Inject;
import org.kframework.attributes.HasLocation;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.inject.RequestScoped;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Set;

@RequestScoped
public class KExceptionManager {
    private final List<KException> exceptions = Collections.synchronizedList(new ArrayList<>());

    public final GlobalOptions options;

    @Inject
    public KExceptionManager(GlobalOptions options) {
        this.options = options;
    }

    public void installForUncaughtExceptions() {
        Thread.setDefaultUncaughtExceptionHandler((t, e) -> {
            String message = "Uncaught exception thrown of type " + e.getClass().getSimpleName();
            if (!options.debug()) {
                message += ".\nPlease rerun your program with the --debug flag to generate a stack trace, "
                        + "and file a bug report at https://github.com/runtimeverification/k/issues";
            }
            exceptions.add(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, message, e));
            print();
        });
    }

    private void printStackTrace(KException e) {
        if (e.getException() != null &&
                (options.debugWarnings || (options.debug() && e.getType() == ExceptionType.ERROR))) {
            e.getException().printStackTrace();
        }
    }

    public void addKException(KException e) {
        registerInternal(e, false);
    }

    public void addAllKException(Collection<KException> kex) {
        for (KException e : kex)
            registerInternal(e, false);
    }

    public void registerCompilerWarning(ExceptionType type, String message) {
        register(type, KExceptionGroup.COMPILER, message, null, null, null);
    }

    public void registerCompilerWarning(ExceptionType type, Set<KEMException> errors, String message, HasLocation node) {
        register(errors, type, KExceptionGroup.COMPILER, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public void registerCompilerWarning(ExceptionType type, String message, HasLocation node) {
        register(type, KExceptionGroup.COMPILER, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public void registerCriticalWarning(ExceptionType type, String message) {
        register(type, KExceptionGroup.CRITICAL, message, null, null, null);
    }

    public void registerCriticalWarning(ExceptionType type, String message, Throwable e) {
        register(type, KExceptionGroup.CRITICAL, message, e, null, null);
    }

    public void registerCriticalWarning(ExceptionType type, String message, HasLocation node) {
        register(type, KExceptionGroup.CRITICAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public void registerInternalWarning(ExceptionType type, String message) {
        register(type, KExceptionGroup.INTERNAL, message, null, null, null);
    }

    public void registerInternalWarning(ExceptionType type, String message, HasLocation node) {
        register(type, KExceptionGroup.INTERNAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public void registerInternalWarning(ExceptionType type, String message, Throwable e) {
        register(type, KExceptionGroup.INTERNAL, message, e, null, null);
    }

    public void registerOuterParserWarning(ExceptionType type, String message, Throwable e, Source source, Location location) {
        register(type, KExceptionGroup.OUTER_PARSER, message, e, location, source);
    }

    public void registerInnerParserWarning(ExceptionType type, String message) {
        register(type, KExceptionGroup.INNER_PARSER, message, null, null, null);
    }

    private void register(ExceptionType type, KExceptionGroup group, String message,
                          Throwable e, Location location, Source source) {
        registerInternal(new KException(type, group, message, source, location, e), true);
    }

    private void register(Set<KEMException> errors, ExceptionType type, KExceptionGroup group, String message,
                          Throwable e, Location location, Source source) {
        if (!options.includesExceptionType(type))
            return;
        KException exception = new KException(type, group, message, source, location, e);
        if (exception.type == ExceptionType.ERROR || options.warnings2errors) {
            errors.add(new KEMException(exception, ExceptionType.ERROR));
        } else {
            registerInternal(exception, false);
        }
    }


    private void registerInternal(KException exception, boolean _throw) {
        if (!options.includesExceptionType(exception.type))
            return;
        if (_throw && (exception.type == ExceptionType.ERROR || options.warnings2errors)) {
            throw new KEMException(exception, ExceptionType.ERROR);
        } else if (options.warnings2errors) {
          exceptions.add(new KException(ExceptionType.ERROR, exception.exceptionGroup, exception.getMessage(), exception.getSource(), exception.getLocation(), exception.getException()));
        } else {
          exceptions.add(exception);
        }
    }

    public void print() {
        Collections.sort(exceptions,
            Comparator.comparing(KException::getSource, Comparator.nullsLast(Comparator.naturalOrder()))
            .thenComparing(KException::getLocation, Comparator.nullsLast(Comparator.naturalOrder()))
            .thenComparing(e -> e.toString(options.verbose)));
        KException last = null;
        synchronized (exceptions) {
            for (KException e : exceptions) {
                if (last != null && last.toString(options.verbose).equals(e.toString(options.verbose))) {
                    continue;
                }
                printStackTrace(e);
                String msg = options.noExcWrap ? e.toString(options.verbose)
                                               : StringUtil.splitLines(e.toString(options.verbose));
                System.err.println(msg);
                last = e;
            }
            exceptions.clear();
        }
    }

    public void registerThrown(KEMException e) {
        KException exception = e.exception;
        if (!options.includesExceptionType(exception.type))
            return;
        if (options.warnings2errors) {
            exceptions.add(new KException(ExceptionType.ERROR, exception.exceptionGroup, exception.getMessage(), exception.getSource(), exception.getLocation(), exception.getException()));
        } else {
            exceptions.add(exception);
        }
    }

    public List<KException> getExceptions() {
        return exceptions;
    }
}
