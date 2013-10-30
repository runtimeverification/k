package org.kframework.backend.java.kil;

/**
 * @author: TraianSF
 */
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

/**
 * Refers to a computation which never completes successfully.
 */
public class Bottom extends Term {

    public Bottom(Kind kind) {
        super(kind);
    }

    @Override
    public boolean isSymbolic() {
        return false;
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
    public void accept(Unifier unifier, Term patten) { }

    @Override
    public void accept(Visitor visitor) { }
}
