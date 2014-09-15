// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

public class BuiltinMgu extends Term {

    public static final Sort SORT = Sort.MGU;

    public static final String EMPTY_MGU = ".Mgu";

    private final SymbolicConstraint constraint;

    private BuiltinMgu(SymbolicConstraint constraint, TermContext context) {
        // YilongL: The kind of a BuiltinMgu should be Kind.KITEM rather than a
        // new created kind for two reasons: 1) an Mgu is a builtin which should
        // be subsorted into KItem; 2) if we assign Mgu its own kind, say MGU,
        // then we have a problem deciding the kind of MguOrError.
        super(Kind.KITEM);
        this.constraint = constraint == null ? new SymbolicConstraint(context)
                : new SymbolicConstraint(constraint, context);
    }

    public static class BuiltinMguOperations {
        public static BuiltinMgu emptyMgu(TermContext context) {
            return new BuiltinMgu(null, context);
        }
    }

    public static BuiltinMgu of(SymbolicConstraint constraint,
            TermContext context) {
        return new BuiltinMgu(constraint, context);
    }

    public SymbolicConstraint constraint() {
        return constraint;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public Sort sort() {
        return SORT;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinMgu)) {
            return false;
        }

        BuiltinMgu mgu = (BuiltinMgu) object;
        return constraint.equals(mgu.constraint);
    }

    @Override
    protected int computeHash() {
        return Utils.HASH_PRIME + constraint.hashCode();
    }

    @Override
    protected boolean computeMutability() {
        return false;
    }

    @Override
    public String toString() {
        return "Mgu(" + constraint.toString() + ")";
    }

}
