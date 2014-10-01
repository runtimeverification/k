// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import java.util.Map;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.AssociativeCommutativeCollection;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.Production;

import com.google.inject.Inject;
import com.google.inject.Provider;

/**
 * An equality between two canonicalized terms.
 */
public class Equality {

    public static final String SEPARATOR = " =? ";

    private final Term leftHandSide;
    private final Term rightHandSide;
    private final TermContext context;

    private TruthValue truthValue = null;

    public Equality(Term leftHandSide, Term rightHandSide, TermContext context) {
        // TODO(YilongL): this seems a little bit ad-hoc...
        if (isTermEquality(leftHandSide) && rightHandSide == BoolToken.TRUE) {
            KList kList = (KList) (((KItem) leftHandSide).kList());
            leftHandSide = kList.get(0);
            rightHandSide = kList.get(1);
        } else if (isTermEquality(rightHandSide) && leftHandSide == BoolToken.TRUE) {
            KList kList = (KList) (((KItem) rightHandSide).kList());
            leftHandSide = kList.get(0);
            rightHandSide = kList.get(1);
        }

        /* arrange the leftHandSide and rightHandSide according to the natural
         * ordering defined for {@code Term} */
        leftHandSide = canonicalize(leftHandSide);
        rightHandSide = canonicalize(rightHandSide);
        if (leftHandSide.compareTo(rightHandSide) > 0) {
            Term term = leftHandSide;
            leftHandSide = rightHandSide;
            rightHandSide = term;
        }

        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.context = context;
    }

    public Term leftHandSide() {
        return leftHandSide;
    }

    public Term rightHandSide() {
        return rightHandSide;
    }

    private boolean isTermEquality(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && ((KLabelConstant) ((KItem) term).kLabel()).label().equals("'_==K_");
    }

    private Term canonicalize(Term term) {
        if (term.kind() == Kind.K || term.kind() == Kind.KLIST) {
            term = KCollection.downKind(term);
        }
        if (term.kind() == Kind.CELL_COLLECTION) {
            term = CellCollection.downKind(term);
        }
        return term;

        // TODO(YilongL): unable to assume that KList is the only possible
        // non-canonicalized term because SymbolicUnifier still use upkind a lot
        // return term instanceof KList ? KCollection.downKind(term) : term;
    }

    public TruthValue truthValue() {
        if (truthValue != null) {
            return truthValue;
        }

        if (isTrue()) {
            truthValue = TruthValue.TRUE;
        } else if (isFalse()) {
            truthValue = TruthValue.FALSE;
        } else {
            truthValue = TruthValue.UNKNOWN;
        }
        return truthValue;
    }

    private boolean isTrue() {
        return !(leftHandSide instanceof Bottom)
                && !(rightHandSide instanceof Bottom)
                && leftHandSide.equals(rightHandSide);
    }

    private boolean isFalse() {
        return context.global().equalityOps.isFalse(this);
    }

    /**
     * Returns an {@code Equality} obtained by applying the {@code substitution} on
     * {@code this} equality.
     *
     * @param substitution
     *            the specified substitution map
     */
    public Equality substitute(Map<Variable, ? extends Term> substitution) {
        Term returnLeftHandSide = leftHandSide.substituteWithBinders(substitution, context);
        Term returnRightHandSide = rightHandSide.substituteWithBinders(substitution, context);
        if (returnLeftHandSide != leftHandSide || returnRightHandSide != rightHandSide) {
            return new Equality(returnLeftHandSide, returnRightHandSide, context);
        } else {
            return this;
        }
    }

    /**
     * Returns an {@code Equality} obtained by applying the {@code substitution} on
     * {@code this} equality and then evaluating pending functions.
     *
     * @param substitution
     *            the specified substitution map
     */
    public Equality substituteAndEvaluate(Map<Variable, ? extends Term> substitution) {
        Term returnLeftHandSide = leftHandSide.substituteAndEvaluate(substitution, context);
        Term returnRightHandSide = rightHandSide.substituteAndEvaluate(substitution, context);
        if (returnLeftHandSide != leftHandSide || returnRightHandSide != rightHandSide) {
            return new Equality(returnLeftHandSide, returnRightHandSide, context);
        } else {
            return this;
        }
    }

    public Equality expandPatterns(SymbolicConstraint constraint, boolean narrowing) {
        Term returnLeftHandSide = leftHandSide.expandPatterns(constraint, narrowing, context);
        Term returnRightHandSide = rightHandSide.expandPatterns(constraint, narrowing, context);
        if (returnLeftHandSide != leftHandSide || returnRightHandSide != rightHandSide) {
            return new Equality(returnLeftHandSide, returnRightHandSide, context);
        } else {
            return this;
        }
    }

    /**
     * Specifies whether this equality can be further decomposed by the
     * unification algorithm of {@code SymbolicUnifier}.
     */
    public boolean isSimplifiableByCurrentAlgorithm() {
        return !leftHandSide.isSymbolic() && !rightHandSide.isSymbolic()
                && !(leftHandSide instanceof BuiltinMap) && !(rightHandSide instanceof BuiltinMap)
                && !(leftHandSide instanceof BuiltinList) && !(rightHandSide instanceof BuiltinList)
                && !(leftHandSide instanceof BuiltinSet) && !(rightHandSide instanceof BuiltinSet);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Equality)) {
            return false;
        }

        Equality equality = (Equality) object;
        return leftHandSide.equals(equality.leftHandSide)
                && rightHandSide.equals(equality.rightHandSide);
    }

    @Override
    public int hashCode() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + leftHandSide.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + rightHandSide.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        return leftHandSide + SEPARATOR + rightHandSide;
    }

    public static class EqualityOperations {

        private final Provider<Definition> definitionProvider;
        private final JavaExecutionOptions options;

        @Inject
        public EqualityOperations(Provider<Definition> definitionProvider, JavaExecutionOptions options) {
            this.definitionProvider = definitionProvider;
            this.options = options;
        }

        /**
         * Checks if a given equality is false.
         *
         * @return {@code true} if this equality is definitely false; otherwise,
         *         {@code false}
         */
        public boolean isFalse(Equality equality) {
            Definition definition = definitionProvider.get();
            Term leftHandSide = equality.leftHandSide;
            Term rightHandSide = equality.rightHandSide;
            if (leftHandSide instanceof Bottom || rightHandSide instanceof Bottom) {
                return true;
            }

            /* both leftHandSide & rightHandSide must have been evaluated before
             * this method is invoked */
            if (leftHandSide.isGround() && rightHandSide.isGround()) {
                return !leftHandSide.equals(rightHandSide);
            }

            if (leftHandSide instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) leftHandSide).unify(rightHandSide)) {
                return true;
            } else if (rightHandSide instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) rightHandSide).unify(leftHandSide)) {
                return true;
            }

            if (leftHandSide instanceof Variable
                    && rightHandSide instanceof org.kframework.backend.java.kil.Collection
                    && ((org.kframework.backend.java.kil.Collection) rightHandSide).hasFrame()
                    && ((org.kframework.backend.java.kil.Collection) rightHandSide).concreteSize() != 0
                    && leftHandSide.equals(((org.kframework.backend.java.kil.Collection) rightHandSide).frame())) {
                return true;
            } else if (rightHandSide instanceof Variable
                    && leftHandSide instanceof org.kframework.backend.java.kil.Collection
                    && ((org.kframework.backend.java.kil.Collection) leftHandSide).hasFrame()
                    && ((org.kframework.backend.java.kil.Collection) leftHandSide).concreteSize() != 0
                    && rightHandSide.equals(((org.kframework.backend.java.kil.Collection) leftHandSide).frame())) {
                return true;
            }

            if (leftHandSide instanceof Variable
                    && rightHandSide instanceof AssociativeCommutativeCollection
                    && ((AssociativeCommutativeCollection) rightHandSide).collectionVariables().contains(leftHandSide)
                    && ((AssociativeCommutativeCollection) rightHandSide).concreteSize() != 0) {
                return true;
            } else if (rightHandSide instanceof Variable
                    && leftHandSide instanceof AssociativeCommutativeCollection
                    && ((AssociativeCommutativeCollection) leftHandSide).collectionVariables().contains(rightHandSide)
                    && ((AssociativeCommutativeCollection) leftHandSide).concreteSize() != 0) {
                return true;
            }

            if (leftHandSide.isExactSort() && rightHandSide.isExactSort()) {
                return !leftHandSide.sort().equals(rightHandSide.sort());
            } else if (leftHandSide.isExactSort()) {
                return !definition.subsorts().isSubsortedEq(
                        rightHandSide.sort(),
                        leftHandSide.sort());
            } else if (rightHandSide.isExactSort()) {
                return !definition.subsorts().isSubsortedEq(
                        leftHandSide.sort(),
                        rightHandSide.sort());
            } else {
                if (leftHandSide instanceof Variable && rightHandSide instanceof KItem
                        && ((KItem) rightHandSide).kLabel() instanceof KLabelConstant
                        && ((KLabelConstant) ((KItem) rightHandSide).kLabel()).isConstructor()) {
                    boolean flag = false;
                    //for (Production production : definition.context().productionsOf(((KLabelConstant) ((KItem) rightHandSide).kLabel()).label())) {
                    for (Production production : ((KLabelConstant) ((KItem) rightHandSide).kLabel()).productions()) {
                        if (definition.subsorts().isSubsortedEq(
                                leftHandSide.sort(),
                                Sort.of(production.getSort()))) {
                            flag = true;
                        }
                    }
                    if (!flag) {
                        return true;
                    }
                }
                if (rightHandSide instanceof Variable && leftHandSide instanceof KItem
                        && ((KItem) leftHandSide).kLabel() instanceof KLabelConstant
                        && ((KLabelConstant) ((KItem) leftHandSide).kLabel()).isConstructor()) {
                    boolean flag = false;
                    //for (Production production : definition.context().productionsOf(((KLabelConstant) ((KItem) leftHandSide).kLabel()).label())) {
                    for (Production production : ((KLabelConstant) ((KItem) leftHandSide).kLabel()).productions()) {
                        if (definition.subsorts().isSubsortedEq(
                                rightHandSide.sort(),
                                Sort.of(production.getSort()))) {
                            flag = true;
                        }
                    }
                    if (!flag) {
                        return true;
                    }
                }
                return !definition.subsorts().hasCommonSubsort(
                        leftHandSide.sort(),
                        rightHandSide.sort());
            }
        }
    }

}