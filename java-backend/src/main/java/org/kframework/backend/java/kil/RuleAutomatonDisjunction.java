// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.utils.BitSet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * A disjunction of terms coming from different rewrite rules.
 * Used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
 */
public class RuleAutomatonDisjunction extends Term implements HasGlobalContext {

    /**
     * (pattern, appearing-in-rules) pairs indexed (via the array) by the pattern's klabel ordinal
     */
    private final Pair<KItem, BitSet>[] kItemDisjunctionsArray;

    /**
     * pairs of variable-rule where it appears, indexed by the variable's sort
     */
    private final List<Pair<Variable, BitSet>>[] variableDisjunctionsArray;
    /**
     * a mapping from Tokens to the rules where they appear in this disjunction
     */
    public final Map<Token, BitSet> tokenDisjunctions;
    private final List<Pair<Term, BitSet>> disjunctions;

    private final GlobalContext global;

    /**
     * Creates the disjunction based on a list of (Term, rules that contain that term).
     * It expects the disjunctions to have already been pushed down the term, i.e., there can be at most
     * one term with a particular KLabel in the list.
     *
     * @param children
     * @param global
     */
    public RuleAutomatonDisjunction(List<Pair<Term, BitSet>> children, GlobalContext global) {
        super(Kind.KITEM);
        this.global = global;
        disjunctions = Collections.unmodifiableList(children);
        this.kItemDisjunctionsArray = new Pair[KLabelConstant.maxOrdinal.get()];
        children.stream()
                .filter(p -> p.getLeft() instanceof KItem)
                .forEach(p -> {
                    this.kItemDisjunctionsArray[((KLabelConstant) ((KItem) p.getLeft()).kLabel()).ordinal()] = (Pair<KItem, BitSet>) (Object) p;
                });


        this.variableDisjunctionsArray = new List[Sort.maxOrdinal.get()];

        global.getDefinition().allSorts().forEach(s -> {
            this.variableDisjunctionsArray[s.ordinal()] = new ArrayList<>((Set<Pair<Variable, BitSet>>) (Object) children.stream()
                    .filter(p -> p.getLeft() instanceof Variable && global.getDefinition().subsorts().isSubsortedEq(p.getLeft().sort(), s))
                    .collect(Collectors.toSet()));
        });

        this.tokenDisjunctions = children.stream()
                .filter(p -> p.getLeft() instanceof Token)
                .collect(Collectors.toMap(p -> (Token) p.getLeft(), p -> p.getRight()));
    }


    /**
     * Gets the (pattern, appearing-in-rules) pair for the klabel.
     */
    public Pair<KItem, BitSet> getKItemPatternForKLabel(KLabelConstant klabel) {
        return this.kItemDisjunctionsArray[klabel.ordinal()];
    }

    /**
     * Gets the variables and the rules where they appear for a sort
     */
    public List<Pair<Variable, BitSet>> getVariablesForSort(Sort sort) {
        return this.variableDisjunctionsArray[sort.ordinal()];
    }

    /**
     * @return all elements of the disjunction. As expected by the disjunction constructor.
     */
    public List<Pair<Term, BitSet>> disjunctions() {
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

    /**
     * @return the maximal KLabel ordinal for the KItem patterns appearing in this disjunction
     */
    public int getKLabelMaxOrdinal() {
        return kItemDisjunctionsArray.length;
    }

    @Override
    public GlobalContext globalContext() {
        return global;
    }
}
