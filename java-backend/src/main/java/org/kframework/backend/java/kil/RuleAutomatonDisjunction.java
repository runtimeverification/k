package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.builtin.KLabels;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;


public class RuleAutomatonDisjunction extends Term {

    public final Pair<KItem, BitSet>[] kItemDisjunctionsArray;
    public final List<Pair<Variable, BitSet>>[] variableDisjunctionsArray;
    private final Map<Sort, Set<Pair<Variable, BitSet>>> variableDisjunctions;
    private final Map<Token, Pair<Token, BitSet>> tokenDisjunctions;

    public RuleAutomatonDisjunction(List<Pair<Term, BitSet>> children, TermContext context) {
        super(Kind.KITEM);
        this.kItemDisjunctionsArray = new Pair[KLabelConstant.cacheSize];
        children.stream()
                .filter(p -> p.getLeft() instanceof KItem)
                .forEach(p -> {
                    this.kItemDisjunctionsArray[((KLabelConstant) ((KItem) p.getLeft()).kLabel()).ordinal()] = (Pair<KItem, BitSet>) (Object) p;
                });

        this.variableDisjunctionsArray = new List[Sort.cache.size()];
        context.definition().allSorts().forEach(s -> {
            this.variableDisjunctionsArray[s.ordinal()] = new ArrayList<>((Set<Pair<Variable, BitSet>>) (Object) children.stream()
                    .filter(p -> p.getLeft() instanceof Variable && context.definition().subsorts().isSubsortedEq(p.getLeft().sort(), s))
                    .collect(Collectors.toSet()));
        });

        this.variableDisjunctions = context.definition().allSorts().stream().collect(Collectors.toMap(
                s -> s,
                s -> (Set<Pair<Variable, BitSet>>) (Object) children.stream()
                        .filter(p -> p.getLeft() instanceof Variable && context.definition().subsorts().isSubsortedEq(p.getLeft().sort(), s))
                        .collect(Collectors.toSet())));
        this.tokenDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof Token)
                .collect(Collectors.toMap(p -> (Token) p.getLeft(), p -> (Pair<Token, BitSet>) (Object) p));
    }


    public Map<Sort, Set<Pair<Variable, BitSet>>> variableDisjunctions() {
        return variableDisjunctions;
    }

    public Map<Token, Pair<Token, BitSet>> tokenDisjunctions() {
        return tokenDisjunctions;
    }

    public List<Pair<Term, BitSet>> disjunctions() {
        List<Pair<Term, BitSet>> disjunctions = new ArrayList<>();
        disjunctions.addAll((java.util.Collection<Pair<Term, BitSet>>) (Object) Arrays.asList(kItemDisjunctionsArray));
//        for (List<Pair<Variable, BitSet>> pairs : variableDisjunctions) {
//            if (pairs != null) {
//                disjunctions.addAll((java.util.Collection<Pair<Term, BitSet>>) (Object) pairs);
//            }
//        }
        ((Map<Sort, Set<Pair<Term, BitSet>>>) (Object) variableDisjunctions).values().forEach(disjunctions::addAll);
        disjunctions.addAll((java.util.Collection<Pair<Term, BitSet>>) (Object) tokenDisjunctions.values());
        disjunctions.removeIf(e -> e == null);
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

        return Arrays.equals(kItemDisjunctionsArray, that.kItemDisjunctionsArray)
                && variableDisjunctions.equals(that.variableDisjunctions)
                && tokenDisjunctions.equals(that.tokenDisjunctions);

    }

    @Override
    protected int computeHash() {
        int result = 1;
        result = 31 * result + Arrays.hashCode(kItemDisjunctionsArray);
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

    @Override
    public String toString() {
        return disjunctions().stream().map(Object::toString).reduce("", (a, b) -> a + " OR " + b);
    }
}
