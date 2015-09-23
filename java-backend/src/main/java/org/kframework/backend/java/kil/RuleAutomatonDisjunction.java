package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;


public class RuleAutomatonDisjunction extends Term {

    private final Map<KLabelConstant, Pair<KItem, Set<Integer>>> kItemDisjunctions;
    private final Map<Sort, Set<Pair<Variable, Set<Integer>>>> variableDisjunctions;
    private final Map<Token, Pair<Token, Set<Integer>>> tokenDisjunctions;

    public RuleAutomatonDisjunction(List<Pair<Term, Set<Integer>>> children, TermContext context) {
        super(Kind.KITEM);
        this.kItemDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof KItem)
                .collect(Collectors.toMap(p -> ((KLabelConstant) ((KItem) p.getLeft()).kLabel()), p -> (Pair<KItem, Set<Integer>>) (Object) p));
        this.variableDisjunctions = context.definition().allSorts().stream().collect(Collectors.toMap(
                s -> s,
                s -> (Set<Pair<Variable, Set<Integer>>>) (Object) children.stream()
                        .filter(p -> p.getLeft() instanceof Variable && context.definition().subsorts().isSubsortedEq(p.getLeft().sort(), s))
                        .collect(Collectors.toSet())));
        this.tokenDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof Token)
                .collect(Collectors.toMap(p -> (Token) p.getLeft(), p -> (Pair<Token, Set<Integer>>) (Object) p));
    }

    public Map<KLabelConstant, Pair<KItem, Set<Integer>>> kItemDisjunctions() {
        return kItemDisjunctions;
    }

    public Map<Sort, Set<Pair<Variable, Set<Integer>>>> variableDisjunctions() {
        return variableDisjunctions;
    }

    public Map<Token, Pair<Token, Set<Integer>>> tokenDisjunctions() {
        return tokenDisjunctions;
    }

    public List<Pair<Term, Set<Integer>>> disjunctions() {
        List<Pair<Term, Set<Integer>>> disjunctions = new ArrayList<>();
        disjunctions.addAll((java.util.Collection<Pair<Term, Set<Integer>>>) (Object) kItemDisjunctions.values());
        ((Map<Sort, Set<Pair<Term, Set<Integer>>>>) (Object) variableDisjunctions).values().forEach(disjunctions::addAll);
        disjunctions.addAll((java.util.Collection<Pair<Term, Set<Integer>>>) (Object) tokenDisjunctions.values());
        return disjunctions;
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
        return false;
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
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
