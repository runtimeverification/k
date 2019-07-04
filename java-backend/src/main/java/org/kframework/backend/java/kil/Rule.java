// Copyright (c) 2013-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import org.apache.commons.collections15.list.UnmodifiableList;
import org.kframework.attributes.Att;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.rewritemachine.GenerateRHSInstructions;
import org.kframework.backend.java.rewritemachine.RHSInstruction;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.definition.HasAtt;
import org.kframework.kil.Attribute;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.kore.K;
import static org.kframework.kore.KORE.KRewrite;


/**
 * A K rule in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Rule extends JavaSymbolicObject<Rule> implements HasAtt {

    private final String label;
    private final Term leftHandSide;
    private final Term rightHandSide;
    private final ImmutableList<Term> requires;
    private final ImmutableList<Term> ensures;
    private final ImmutableSet<Variable> freshConstants;
    private final ImmutableSet<Variable> freshVariables;
    private final ConjunctiveFormula lookups;
    private final ImmutableSet<String> matchingSymbols;

    /**
     * Instructions for evaluating side condition of rule.
     */
    private final List<ImmutableList<RHSInstruction>> instructionsOfRequires;
    /**
     * Instructions for evaluating side condition of rule.
     */
    private final List<ImmutableList<RHSInstruction>> instructionsOfLookups;
    private final List<RHSInstruction> rhsInstructions;

    private final Set<Variable> matchingVariables;

    // TODO(YilongL): make it final
    private boolean isSortPredicate;
    private final Sort predSort;
    private final KItem sortPredArg;

    public Rule(
            String label,
            Term leftHandSide,
            Term rightHandSide,
            List<Term> requires,
            List<Term> ensures,
            Set<Variable> freshConstants,
            Set<Variable> freshVariables,
            ConjunctiveFormula lookups,
            Att att) {
        super(att);
        this.label = label;
        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.requires = ImmutableList.copyOf(requires);
        this.ensures = ImmutableList.copyOf(ensures);
        this.freshConstants = ImmutableSet.copyOf(freshConstants);
        this.freshVariables = ImmutableSet.copyOf(freshVariables);
        this.lookups = lookups;
        this.matchingSymbols = att.contains(Attribute.MATCHING_KEY) ? ImmutableSet.copyOf(att.get(Attribute.MATCHING_KEY).split(",")) : ImmutableSet.of();

        isSortPredicate = isFunction() && definedKLabel().isSortPredicate();
        if (isSortPredicate) {
            predSort = definedKLabel().getPredicateSort();

            if (leftHandSide instanceof KItem
                    && rightHandSide.equals(BoolToken.TRUE)
                    && ((KList) ((KItem) leftHandSide).kList()).concreteSize() == 1) {
                Term arg = ((KList) ((KItem) leftHandSide).kList()).get(0);
                sortPredArg = arg instanceof KItem ? (KItem) arg : null;
            } else {
                sortPredArg = null;
            }

            if (sortPredArg == null) {
                isSortPredicate = false;

                /*
                 * YilongL: the right-hand side of the sort predicate rule
                 * is not necessarily {@code BoolToken#True}? for example:
                 *     rule isNat(I:Int) => '_>=Int_(I:Int,, Int(#"0"))
                 */
                // TODO(YilongL): properly re-implement support for sort predicate rules
//                GlobalSettings.kem.registerCriticalWarning("Unexpected sort predicate rule: " + this, null, this);
            }
        } else {
            predSort = null;
            sortPredArg = null;
        }

        GenerateRHSInstructions rhsVisitor = new GenerateRHSInstructions();
        rightHandSide.accept(rhsVisitor);
        this.rhsInstructions = rhsVisitor.getInstructions();

        instructionsOfRequires = new ArrayList<>();
        for (Term require : requires) {
            GenerateRHSInstructions visitor = new GenerateRHSInstructions();
            require.accept(visitor);
            instructionsOfRequires.add(visitor.getInstructions());
        }
        instructionsOfLookups = new ArrayList<>();
        for (Equality equality : lookups.equalities()) {
            GenerateRHSInstructions visitor = new GenerateRHSInstructions();
            equality.leftHandSide().accept(visitor);
            instructionsOfLookups.add(visitor.getInstructions());
        }

        matchingVariables = ImmutableSet.copyOf(Sets.union(
                leftHandSide.variableSet(),
                Sets.union(
                        lookups.variableSet(),
                        requires.stream().map(Term::variableSet).flatMap(Set::stream).collect(Collectors.toSet()))));
    }

    public String label() {
        return label;
    }

    public ImmutableList<Term> requires() {
        return requires;
    }

    public ImmutableList<Term> ensures() {
        return ensures;
    }

    public K toKRewrite() {
        return KRewrite(leftHandSide, rightHandSide, att());
    }

    public ConstrainedTerm createLhsPattern(TermContext termContext) {
        // TODO(YilongL): remove TermContext from the signature once
        // ConstrainedTerm doesn't hold a TermContext anymore
        return new ConstrainedTerm(
                leftHandSide,
                ConjunctiveFormula.of(lookups).addAll(requires),
                termContext);
    }

    public ConstrainedTerm createLhsPattern(TermContext termContext, int idx) {
        // TODO(YilongL): remove TermContext from the signature once
        // ConstrainedTerm doesn't hold a TermContext anymore
        return new ConstrainedTerm(
                (Term) ((KList) ((KItem) leftHandSide).kList()).items().get(idx-1), // leftHandSide,
                ConjunctiveFormula.of(lookups).addAll(requires),
                termContext);
    }

    public ConjunctiveFormula getRequires() {
        return ConjunctiveFormula.of(lookups).addAll(requires);
    }

    public ConjunctiveFormula getEnsures(GlobalContext global) {
        return ConjunctiveFormula.of(global).addAll(ensures);
    }

    public ImmutableSet<Variable> freshConstants() {
        return freshConstants;
    }

    public ImmutableSet<Variable> freshVariables() {
        return freshVariables;
    }

    /**
     * @return {@code true} if this rule is a sort predicate rule; otherwise,
     *         {@code false}
     */
    public boolean isSortPredicate() {
        return isSortPredicate;
    }

    /**
     * Gets the predicate sort if this rule is a sort predicate rule.
     */
    public Sort predicateSort() {
        assert isSortPredicate;

        return predSort;
    }

    /**
     * Gets the argument of the sort predicate if this rule is a sort predicate rule.
     */
    public KItem sortPredicateArgument() {
        assert isSortPredicate;

        return sortPredArg;
    }

    public boolean isFunction() {
        return att().contains(Attribute.FUNCTION_KEY)
               && !att().contains(Attribute.PATTERN_FOLDING_KEY);
    }

    public boolean isConcrete() {
        return att().contains(Attribute.CONCRETE_FUNCTION_KEY);
    }

    public boolean isAnywhere() {
        return att().contains(Attribute.ANYWHERE_KEY);
    }

    public boolean isPattern() {
        return att().contains(Attribute.PATTERN_KEY);
    }

    public boolean isLemma() {
        return att().contains(Attribute.LEMMA_KEY);
    }

    /**
     * Returns the KLabel constant defined by this rule (either a function or a pattern).
     */
    public KLabelConstant definedKLabel() {
        assert isFunction() || isPattern();

        return (KLabelConstant) ((KItem) leftHandSide).kLabel();
    }

    public KLabelConstant anywhereKLabel() {
        assert isAnywhere();

        return (KLabelConstant) ((KItem) leftHandSide).kLabel();
    }

    public Term leftHandSide() {
        return leftHandSide;
    }

    public ConjunctiveFormula lookups() {
        return lookups;
    }

    public Term rightHandSide() {
        return rightHandSide;
    }

    public List<ImmutableList<RHSInstruction>> instructionsOfRequires() {
        return UnmodifiableList.decorate(instructionsOfRequires);
    }

    public List<ImmutableList<RHSInstruction>> instructionsOfLookups() {
        return UnmodifiableList.decorate(instructionsOfLookups);
    }

    public List<RHSInstruction> rhsInstructions() {
        return rhsInstructions;
    }

    public Set<Variable> matchingVariables() {
        return matchingVariables;
    }

    public ImmutableSet<String> matchingSymbols() {
        return matchingSymbols;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Rule)) {
            return false;
        }

        Rule rule = (Rule) object;
        return label.equals(rule.label)
                && leftHandSide.equals(rule.leftHandSide)
                && rightHandSide.equals(rule.rightHandSide)
                && requires.equals(rule.requires)
                && ensures.equals(rule.ensures)
                && lookups.equals(rule.lookups)
                && freshConstants.equals(rule.freshConstants);
    }

    @Override
    public int hashCode() {
        int h = hashCode;
        if (h == Constants.NO_HASHCODE) {
            h = 1;
            h = h * Constants.HASH_PRIME + label.hashCode();
            h = h * Constants.HASH_PRIME + leftHandSide.hashCode();
            h = h * Constants.HASH_PRIME + rightHandSide.hashCode();
            h = h * Constants.HASH_PRIME + requires.hashCode();
            h = h * Constants.HASH_PRIME + ensures.hashCode();
            h = h * Constants.HASH_PRIME + lookups.hashCode();
            h = h * Constants.HASH_PRIME + freshConstants.hashCode();
            h = h == 0 ? 1 : h;
            hashCode = h;
        }
        return h;
    }

    @Override
    public String toString() {
        String string = "rule ";
        if ((label != null) && (!label.isEmpty()))
            string += "[" + label + "]: ";
        string += leftHandSide + " => " + rightHandSide;
        if (requires != null) {
            string += " requires " + requires;
        }
        if (!lookups.equalities().isEmpty()) {
            if (requires == null) {
                string += " when ";
            } else {
                string += " " + ConjunctiveFormula.SEPARATOR + " ";
            }
            string += lookups;
        }
        if (ensures != null) {
            string += " ensures " + ensures;
        }
        string += " [" + "Location: " + location() + ", " + source() + "]";
        return string;
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
