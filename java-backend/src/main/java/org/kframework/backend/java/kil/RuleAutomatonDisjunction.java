package org.kframework.backend.java.kil;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;


public class RuleAutomatonDisjunction extends Term {

    private final Map<KLabelConstant, Pair<Term, Set<Integer>>> kItemDisjunctions;
    private final Map<Sort, List<Pair<Variable, Set<Integer>>>> variableDisjunctions;
    private final Map<Token, Pair<Token, Set<Integer>>> tokenDisjunctions;

    public RuleAutomatonDisjunction(List<Pair<Term, Set<Integer>>> children) {
        super(Kind.KITEM);
        this.kItemDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof KItem)
                .collect(Collectors.toMap(p -> ((KLabelConstant) ((KItem) p.getLeft()).kLabel()), p -> p));
        this.variableDisjunctions = (Map<Sort, List<Pair<Variable, Set<Integer>>>>) (Object) children.stream()
                .filter(p -> p.getLeft() instanceof Variable)
                .collect(Collectors.groupingBy(p -> p.getLeft().sort()));
        this.tokenDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof Token)
                .collect(Collectors.toMap(p -> (Token) p.getLeft(), p -> (Pair<Token, Set<Integer>>) (Object) p));
    }

    @Override
    public boolean isExactSort() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isSymbolic() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Sort sort() {
        throw new UnsupportedOperationException();
    }

    @Override
    protected boolean computeMutability() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        RuleAutomatonDisjunction that = (RuleAutomatonDisjunction) o;

        return kItemDisjunctions.equals(that.kItemDisjunctions)
                && variableDisjunctions.equals(that.variableDisjunctions)
                && tokenDisjunctions.equals(that.tokenDisjunctions);

    }

    @Override
    protected int computeHash() {
        int result = 1;
        result = 31 * result + kItemDisjunctions.hashCode();
        result = 31 * result + variableDisjunctions.hashCode();
        result = 31 * result + tokenDisjunctions.hashCode();
        return result;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) { }

}
