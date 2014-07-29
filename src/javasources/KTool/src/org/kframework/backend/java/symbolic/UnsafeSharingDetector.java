// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;

import org.kframework.backend.java.kil.Immutable;
import org.kframework.backend.java.kil.JavaSymbolicObject;
import org.kframework.backend.java.kil.Term;

/**
 * Traverses a {@code Term} and detects unsafe sharing of mutable sub-terms.
 * Used for debugging the new rewrite engine which allows mutable terms.
 *
 * @author YilongL
 *
 */
public class UnsafeSharingDetector extends PrePostVisitor {

    private final Set<Term> visitedTerms = Collections.newSetFromMap(new IdentityHashMap<Term, Boolean>());

    public static void visitTerm(Term term) {
        term.accept(new UnsafeSharingDetector());
    }

    private UnsafeSharingDetector() {
        preVisitor.addVisitor(new SharedMutableTermChecker());
    }

    private class SharedMutableTermChecker extends LocalVisitor {

        @Override
        public void visit(JavaSymbolicObject object) {
            throw new UnsupportedOperationException(
                    UnsafeSharingDetector.this.getName() + " should only be applied on Terms.");
        }

        @Override
        public void visit(Term term) {
            if (term instanceof Immutable || !term.hasCell()) {
                this.proceed = false;
                return;
            }

            if (visitedTerms.contains(term)) {
                throw new AssertionError("Found shared mutable term:\n" + term);
            }

            visitedTerms.add(term);
            return;
        }
    }
}
