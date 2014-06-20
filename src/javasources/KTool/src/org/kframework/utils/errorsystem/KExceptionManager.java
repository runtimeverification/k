// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;

import java.util.ArrayList;
import java.util.List;

public class KExceptionManager {
    private final List<KException> exceptions = new ArrayList<KException>();
    
    private GlobalOptions options;
    
    public KExceptionManager(GlobalOptions options) {
        this.options = options;
    }

    public void register(KException exception) {
        exceptions.add(exception);
        if (exception.type == ExceptionType.ERROR)
            throw new KEMException(exception);
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
            super();
            this.exception = e;
        }
    }

    public List<KException> getExceptions() {
        return exceptions;
    }
}
