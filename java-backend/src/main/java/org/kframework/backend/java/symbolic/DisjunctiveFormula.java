// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.HasGlobalContext;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.CollectionInternalRepresentation;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
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
public class DisjunctiveFormula extends Term implements CollectionInternalRepresentation, HasGlobalContext {

    private final PersistentUniqueList<ConjunctiveFormula> conjunctions;

    private transient final GlobalContext global;

    public DisjunctiveFormula(Collection<ConjunctiveFormula> conjunctions, GlobalContext global) {
        super(Kind.KITEM);
        this.conjunctions = conjunctions instanceof PersistentUniqueList ?
                (PersistentUniqueList<ConjunctiveFormula>) conjunctions :
                PersistentUniqueList.<ConjunctiveFormula>empty().plusAll(conjunctions);
        this.global = global;
    }

    public PersistentUniqueList<ConjunctiveFormula> conjunctions() {
        return conjunctions;
    }

    public GlobalContext globalContext() {
        return global;
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
    public List<Term> getKComponents() {
        return conjunctions.stream().map(ConjunctiveFormula::toKore).collect(Collectors.toList());
    }

    @Override
    public KLabel constructorLabel() {
        return KLabelConstant.of("'_orBool_", global.getDefinition());
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

}
