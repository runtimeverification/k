package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.backend.java.symbolic.Matchable;
import org.kframework.backend.java.symbolic.SubstitutionTransformer;
import org.kframework.backend.java.symbolic.Transformable;
import org.kframework.backend.java.symbolic.VariableVisitor;
import org.kframework.backend.java.symbolic.Visitable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.HashMap;
import java.util.Set;
import java.util.Map;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 12:56 PM
 * To change this template use File | Settings | File Templates.
 */
public abstract class Term extends ASTNode implements Matchable, Transformable, Visitable {

    protected final Kind kind;

    protected Term(Kind kind) {
        this.kind = kind;
    }

    /**
     * @return the string representation of the kind of this term
     * (BuiltinConstant, Cell, CellCollection, K, KLabel, KList, KSequence, Map, Variable).
     */
    public Kind getKind() {
        return kind;
    }

    public boolean isGround() {
        return variableSet().isEmpty();
    }

    public abstract boolean isSymbolic();

    public Term substitute(Map<Variable, Term> substitution, Context context) {
        if (substitution.isEmpty() || isGround()) {
            return this;
        }

        SubstitutionTransformer transformer = new SubstitutionTransformer(substitution, context);
        return (Term) accept(transformer);
    }

    public Term substitute(Variable variable, Term term, Context context) {
        Map<Variable, Term> substitution = new HashMap<Variable, Term>();
        substitution.put(variable, term);
        return substitute(substitution, context);
    }

    public Set<Variable> variableSet() {
        VariableVisitor visitor = new VariableVisitor();
        accept(visitor);
        return visitor.getVariableSet();
    }


    public static Term of(org.kframework.kil.Term kilTerm, Context context) {
        try {
            return (Term) kilTerm.accept(new KILtoBackendJavaKILTransformer(context));
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }
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
