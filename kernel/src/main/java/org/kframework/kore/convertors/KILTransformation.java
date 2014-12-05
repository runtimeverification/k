// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.function.Function;

import org.kframework.kil.ASTNode;

public class KILTransformation<R> implements Function<ASTNode, R> {

    @SuppressWarnings("serial")
    static class VisitingException extends RuntimeException {
        VisitingException(String message, Exception e) {
            super(message, e);
        }
    }

    @SuppressWarnings("unchecked")
    public R apply(ASTNode t) {
        try {
            Method visitorMethod = this.getClass().getDeclaredMethod("apply", t.getClass());
            return (R) visitorMethod.invoke(this, t);
        } catch (NoSuchMethodException | SecurityException | IllegalAccessException
                | IllegalArgumentException e) {
            throw new VisitingException(makeErrorMessage(t), e);
        } catch (InvocationTargetException e) {
            if (e.getCause() instanceof InvocationTargetException)
                throw (VisitingException) e.getCause();
            else if (e.getCause() instanceof RuntimeException)
                throw (RuntimeException) e.getCause();
            else
                throw new VisitingException(makeErrorMessage(t), e);
        }
    }

    public String makeErrorMessage(ASTNode t) {
        return t.toString() + " at location " + t.getLocation() + " in file " + t.getSource() + " of class "
                + t.getClass().toString();
    }
}
