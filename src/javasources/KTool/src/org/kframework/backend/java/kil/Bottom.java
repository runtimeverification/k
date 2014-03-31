package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

/**
 * Refers to a computation which never completes successfully.
 * A {@link org.kframework.backend.java.symbolic.SymbolicConstraint.Equality} instance between
 * bottom and anything else is false and makes the entire constraint false.
 *
 * @see org.kframework.backend.java.symbolic.SymbolicConstraint
 * 
 * @author TraianSF
 */
public class Bottom extends Term {

    public Bottom(Kind kind) {
        super(kind);
    }

    @Override
    public boolean isExactSort() {
        return false;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public String sort() {
        return kind.toString();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Bottom)) {
            return false;
        }

        Bottom bottom = (Bottom) object;
        return kind == bottom.kind;
    }

    @Override
    public int hashCode() {
        return kind.hashCode();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return this;
    }
    
    @Override
    public void accept(Matcher matcher, Term pattern) { 
        // TODO(YilongL): why not throw an exception here?
    }

    @Override
    public void accept(Unifier unifier, Term pattern) { }

    @Override
    public void accept(Visitor visitor) { }
}
