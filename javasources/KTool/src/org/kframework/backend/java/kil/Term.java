package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Evaluator;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.backend.java.symbolic.Unifiable;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;

import java.util.Collections;
import java.util.Map;


/**
 * A K term in the internal representation of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public abstract class Term extends JavaSymbolicObject implements Unifiable, Transformable {

    protected final Kind kind;

    protected Term(Kind kind) {
        this.kind = kind;
    }

    /**
     * Translates a term from the generic KIL representation ({@link org.kframework.kil.Term}) to
     * the Java Rewrite Engine internal representation
     * ({@link org.kframework.backend.java.kil.Term}).
     */
    public static Term of(org.kframework.kil.Term kilTerm, Definition definition) {
        KILtoBackendJavaKILTransformer transformer
                = new KILtoBackendJavaKILTransformer(definition.context());
        return transformer.transformTerm(kilTerm, definition);
    }

    /**
     * Returns {@code true} if this term does not contain any variables.
     */
    public boolean isGround() {
        return super.variableSet().isEmpty();
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
    public Term evaluate(Definition definition) {
        return (Term) this.accept(new Evaluator(definition));
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by applying substitution.
     */
    public Term substitute(Map<Variable, ? extends Term> substitution, Definition definition) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        return (Term) accept(new SubstitutionTransformer(substitution, definition));
    }

    /**
     * Returns a new {@code Term} instance obtained from this term by substituting variable with
     * term.
     */
    public Term substitute(Variable variable, Term term, Definition definition) {
        return substitute(Collections.singletonMap(variable, term), definition);
    }

}
