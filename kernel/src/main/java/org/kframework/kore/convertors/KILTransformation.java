// Copyright (c) K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.Method;
import java.util.function.Function;

import org.kframework.kil.ASTNode;
import org.kframework.utils.errorsystem.KEMException;

public class KILTransformation<R> implements Function<ASTNode, R> {

    @SuppressWarnings("serial")
    static class VisitingException extends RuntimeException {
        VisitingException(String message, Throwable e) {
            super(message, e);
        }
    }

    // DISABLE EXCEPTION CHECKING
    public R apply(ASTNode t) {
        try {
            MethodHandles.Lookup lookup = MethodHandles.lookup();
            Method visitMethod = this.getClass().getDeclaredMethod("apply", t.getClass());
            MethodHandle visitMethodHandle = lookup.unreflect(visitMethod);
            return (R) visitMethodHandle.invoke(this, t);
        } catch (NoSuchMethodException e) {
            throw new VisitingException("Visitor " + this.getClass()
                    + " is missing a definition for visit(" + t.getClass() + ")"
                    + ". Encounteed when visiting " + makeErrorMessage(t), e);
        // DISABLE EXCEPTION CHECKSTYLE
        } catch (VisitingException | KEMException e) {
            throw e;
        } catch (Throwable e) {
            throw new VisitingException(makeErrorMessage(t), e);
        }
        // ENABLE EXCEPTION CHECKSTYLE
    }
    // ENABLE EXCEPTION CHECKING

    public String makeErrorMessage(ASTNode t) {
        return t.toString() + " at location " + t.getLocation() + " in file " + t.getSource()
                + " of class " + t.getClass().toString();
    }
}
