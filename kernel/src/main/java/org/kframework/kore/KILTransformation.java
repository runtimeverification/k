package org.kframework.kore;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.function.Function;

import org.kframework.kil.Term;

public class KILTransformation<R> implements Function<Term, R> {

    @SuppressWarnings("serial")
    static class VisitingException extends RuntimeException {
        VisitingException(Throwable e) {
            super(e);
        }
    }

    @SuppressWarnings("unchecked")
    public R apply(Term t) {
        Method visitorMethod;
        try {
            visitorMethod = this.getClass().getDeclaredMethod("apply",
                    new Class[] { t.getClass() });
            return (R) visitorMethod.invoke(this, t);
        } catch (NoSuchMethodException | SecurityException | IllegalAccessException
                | IllegalArgumentException | InvocationTargetException e) {
            throw new VisitingException(e);
        }
    }
}
