package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;
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

    private final String kind;

    protected Term(String kind) {
        this.kind = kind;
    }

    /**
     * @return the string representation of the kind of this term
     * (BuiltinConstant, Cell, CellCollection, K, KLabel, KList, KSequence, Map, Variable).
     */
    public String getKind() {
        return kind;
    }

    public abstract boolean isSymbolic();

    public Term substitute(Map<Variable, Term> substitution) {
        SubstitutionTransformer transformer = new SubstitutionTransformer(substitution);
        return (Term) accept(transformer);
    }

    public Term substitute(Variable variable, Term term) {
        Map<Variable, Term> substitution = new HashMap<Variable, Term>();
        substitution.put(variable, term);
        return substitute(substitution);
    }

    public Set<Variable> variableSet() {
        VariableVisitor visitor = new VariableVisitor();
        accept(visitor);
        return visitor.getVariableSet();
    }

    @Override
    public ASTNode accept(org.kframework.kil.visitors.Transformer transformer) throws TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(org.kframework.kil.visitors.Visitor visitor) {
        throw new UnsupportedOperationException();
    }

}
