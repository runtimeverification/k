// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.CollectionInternalRepresentation;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.kil.ASTNode;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A disjunction of conjunctions.
 *
 * @see org.kframework.backend.java.symbolic.ConjunctiveFormula
 */
public class DisjunctiveFormula extends Term implements CollectionInternalRepresentation {

    private final PersistentUniqueList<ConjunctiveFormula> conjunctions;

    private transient final TermContext context;

    public DisjunctiveFormula(Collection<ConjunctiveFormula> conjunctions, TermContext context) {
        super(Kind.KITEM);
        this.conjunctions = conjunctions instanceof PersistentUniqueList ?
                (PersistentUniqueList<ConjunctiveFormula>) conjunctions :
                PersistentUniqueList.<ConjunctiveFormula>empty().plusAll(conjunctions);
        this.context = context;
    }

    public PersistentUniqueList<ConjunctiveFormula> conjunctions() {
        return conjunctions;
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return Sort.BOOL;
    }

    @Override
    protected boolean computeMutability() {
        return false;
    }

    @Override
    public Term toKore() {
        return toKore(context);
    }

    @Override
    public List<Term> getKComponents() {
        return conjunctions.stream().map(ConjunctiveFormula::toKore).collect(Collectors.toList());
    }

    @Override
    public KLabel constructorLabel() {
        return KLabelConstant.of("'_orBool_", context.definition());
    }

    @Override
    public Token unit() {
        return BoolToken.FALSE;
    }

    @Override
    protected int computeHash() {
        return conjunctions.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof DisjunctiveFormula)) {
            return false;
        }

        DisjunctiveFormula disjunction = (DisjunctiveFormula) object;
        return conjunctions.equals(disjunction.conjunctions);
    }

    @Override
    public String toString() {
        return toKore().toString();
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        throw new UnsupportedOperationException();
    }

}
