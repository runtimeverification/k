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
import java.util.List;

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
                        + "and file a bug report at https://github.com/kframework/k/issues";
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

    public void registerCompilerWarning(String message) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, null, null);
    }

    public void registerCompilerWarning(String message, HasLocation node) {
        register(ExceptionType.WARNING, KExceptionGroup.COMPILER, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public void registerCriticalWarning(String message) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, null, null);
    }

    public void registerCriticalHiddenWarning(String message) {
        register(ExceptionType.HIDDENWARNING, KExceptionGroup.CRITICAL, message, null, null, null);
    }

    public void registerCriticalWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, e, null, null);
    }

    public void registerCriticalWarning(String message, HasLocation node) {
        register(ExceptionType.WARNING, KExceptionGroup.CRITICAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    public void registerInternalWarning(String message) {
        register(ExceptionType.WARNING, KExceptionGroup.INTERNAL, message, null, null, null);
    }

    public void registerInternalWarning(String message, Throwable e) {
        register(ExceptionType.WARNING, KExceptionGroup.INTERNAL, message, e, null, null);
    }

    public void registerInternalHiddenWarning(String message, Throwable e) {
        register(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, message, e, null, null);
    }

    public void registerInternalHiddenWarning(String message) {
        register(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, message, null, null, null);
    }

    public void registerInternalHiddenWarning(String message, HasLocation node) {
        register(ExceptionType.HIDDENWARNING, KExceptionGroup.INTERNAL, message, null, node.location().orElse(null), node.source().orElse(null));
    }

    private void register(ExceptionType type, KExceptionGroup group, String message,
                          Throwable e, Location location, Source source) {
        registerInternal(new KException(type, group, message, source, location, e), true);
    }

    private void registerInternal(KException exception, boolean _throw) {
        if (!options.warnings.includesExceptionType(exception.type))
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
        Collections.sort(exceptions, (arg0, arg1) ->
                arg0.toString(options.verbose).compareTo(arg1.toString(options.verbose)));
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
        }
    }

    public void registerThrown(KEMException e) {
        exceptions.add(e.exception);
    }

    public List<KException> getExceptions() {
        return exceptions;
    }
}
