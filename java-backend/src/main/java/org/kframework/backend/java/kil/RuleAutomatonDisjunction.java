// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.utils.BitSet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * A disjunction of terms coming from different rewrite rules.
 * Used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
 */
public class RuleAutomatonDisjunction extends Term {

    /**
     * the KApplies in the disjunction, indexed (via the array) by their source rule
     */
    public final Pair<KItem, BitSet>[] kItemDisjunctionsArray;
    public final List<Pair<Variable, BitSet>>[] variableDisjunctionsArray;
    public final Map<Token, Pair<Token, BitSet>> tokenDisjunctions;

    public final BitSet ruleMask;

    public RuleAutomatonDisjunction(List<Pair<Term, BitSet>> children, TermContext context) {
        super(Kind.KITEM);
        this.kItemDisjunctionsArray = new Pair[KLabelConstant.cacheSize()];
        children.stream()
                .filter(p -> p.getLeft() instanceof KItem)
                .forEach(p -> {
                    this.kItemDisjunctionsArray[((KLabelConstant) ((KItem) p.getLeft()).kLabel()).ordinal()] = (Pair<KItem, BitSet>) (Object) p;
                });

        synchronized (Sort.cache) {
            this.variableDisjunctionsArray = new List[Sort.cache.size()];
        }
        context.definition().allSorts().forEach(s -> {
            this.variableDisjunctionsArray[s.ordinal()] = new ArrayList<>((Set<Pair<Variable, BitSet>>) (Object) children.stream()
                    .filter(p -> p.getLeft() instanceof Variable && context.definition().subsorts().isSubsortedEq(p.getLeft().sort(), s))
                    .collect(Collectors.toSet()));
        });

        this.tokenDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof Token)
                .collect(Collectors.toMap(p -> (Token) p.getLeft(), p -> (Pair<Token, BitSet>) (Object) p));

        ruleMask = BitSet.apply(context.definition().reverseRuleTable.size());
    }

    public Map<Token, Pair<Token, BitSet>> tokenDisjunctions() {
        return tokenDisjunctions;
    }

    public List<Pair<Term, BitSet>> disjunctions() {
        Set<Pair<Term, BitSet>> disjunctions = new HashSet<>();
        disjunctions.addAll((java.util.Collection<Pair<Term, BitSet>>) (Object) Arrays.asList(kItemDisjunctionsArray));
        ((List<List<Pair<Term, BitSet>>>) (Object) Arrays.asList(variableDisjunctionsArray)).stream().filter(l -> l != null).forEach(disjunctions::addAll);
        disjunctions.addAll((java.util.Collection<Pair<Term, BitSet>>) (Object) tokenDisjunctions.values());
        disjunctions.removeIf(e -> e == null);
        return new ArrayList<>(disjunctions);
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
                && Arrays.equals(variableDisjunctionsArray, that.variableDisjunctionsArray)
                && tokenDisjunctions.equals(that.tokenDisjunctions);

    }

    @Override
    protected int computeHash() {
        int result = 1;
        result = 31 * result + Arrays.hashCode(kItemDisjunctionsArray);
        result = 31 * result + Arrays.hashCode(variableDisjunctionsArray);
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
