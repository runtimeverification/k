package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.backend.java.symbolic.Unifiable;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.VariableVisitor;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collections;
import java.util.Set;
import java.util.Map;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends ASTNode implements Unifiable, Transformable, Visitable {

    protected final Kind kind;

    protected Term(Kind kind) {
        this.kind = kind;
    }

    /**
     * Translates a term from the generic KIL representation ({@link org.kframework.kil.Term}) to
     * the Java Rewrite Engine internal representation
     * ({@link org.kframework.backend.java.kil.Term}).
     */
    public static Term of(org.kframework.kil.Term kilTerm, Context context) {
        try {
            return (Term) kilTerm.accept(new KILtoBackendJavaKILTransformer(context));
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }
    }

    /**
     * Returns {@code true} if this term does not contain any variables.
     */
    public boolean isGround() {
        return variableSet().isEmpty();
    }

    /**
     * Returns {@code true} if a unification task between this term and another term cannot be
     * further decomposed into simpler unification tasks.
     */
    public abstract boolean isSymbolic();

    /**
     * Returns the kind of this term (Cell, CellCollection, KItem, K, KLabel, KList, or Map).
     */
    public Kind kind() {
        return kind;
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by evaluating pending
     * function and predicate operations.
     */
    public Term evaluate(Context context) {
        return (Term) this.accept(new Evaluator(context));
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying substitution.
     */
    public Term substitute(Map<Variable, ? extends Term> substitution, Context context) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        return (Term) accept(new SubstitutionTransformer((Map<Variable, Term>) substitution, context));
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by substituting variable with
     * term.
     */
    public Term substitute(Variable variable, Term term, Context context) {
        return substitute(Collections.singletonMap(variable, term), context);
    }

    /**
     * Returns a {@code Set} view of the variables in this term.
     */
    public Set<Variable> variableSet() {
        VariableVisitor visitor = new VariableVisitor();
        accept(visitor);
        return visitor.getVariableSet();
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(org.kframework.kil.visitors.Transformer transformer)
            throws TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(org.kframework.kil.visitors.Visitor visitor) {
        throw new UnsupportedOperationException();
    }

}
