// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.function.Function;

import org.kframework.kil.ASTNode;

public class KILTransformation<R> implements Function<ASTNode, R> {

    @SuppressWarnings("serial")
    static class VisitingException extends RuntimeException {
        VisitingException(Throwable e, Class cls) {
            super(e.getMessage() + " - " + cls.getName(), e);
        }
    }

    @SuppressWarnings("unchecked")
    public R apply(ASTNode t) {
        try {
            Method visitorMethod = this.getClass().getDeclaredMethod("apply", t.getClass());
            return (R) visitorMethod.invoke(this, t);
        } catch (NoSuchMethodException | SecurityException | IllegalAccessException
                | IllegalArgumentException e) {
            throw new VisitingException(e, t.getClass());
        } catch (InvocationTargetException e) {
            throw new VisitingException(e.getTargetException(), t.getClass());
        }
    }
}
