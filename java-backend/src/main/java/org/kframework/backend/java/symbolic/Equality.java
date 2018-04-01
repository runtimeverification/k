// Copyright (c) 2014-2018 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import java.io.Serializable;
import java.util.stream.IntStream;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.Constants;

import com.google.inject.Provider;
import org.kframework.builtin.KLabels;

import org.pcollections.PSet;

/**
 * An equality between two canonicalized terms.
 */
public class Equality implements Serializable {

    public static final String SEPARATOR = " =? ";

    private final Term leftHandSide;
    private final Term rightHandSide;
    private final GlobalContext global;

    private TruthValue truthValue = null;

    public Equality(Term leftHandSide, Term rightHandSide, GlobalContext global) {
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

        leftHandSide = canonicalize(leftHandSide);
        rightHandSide = canonicalize(rightHandSide);
        // TODO(YilongL): unable to do the following because the order of lhs
        // and rhs matters when checking implication
//        /* arrange the leftHandSide and rightHandSide according to the natural
//         * ordering defined for {@code Term} */
//        if (leftHandSide.compareTo(rightHandSide) > 0) {
//            Term term = leftHandSide;
//            leftHandSide = rightHandSide;
//            rightHandSide = term;
//        }

        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.global = global;
    }

    public Term leftHandSide() {
        return leftHandSide;
    }

    public Term rightHandSide() {
        return rightHandSide;
    }

    public PSet<Variable> variableSet() {
        PSet<Variable> vSet = leftHandSide.variableSet();
        vSet.plusAll(rightHandSide.variableSet());
        return vSet;
    }

    private boolean isTermEquality(Term term) {
        return term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabelConstant
                && ((KLabelConstant) ((KItem) term).kLabel()).label().equals("_==K_");
    }

    private Term canonicalize(Term term) {
        if (term.kind() == Kind.K || term.kind() == Kind.KLIST) {
            term = KCollection.downKind(term);
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

    public boolean isTrue() {
        return !(leftHandSide instanceof Bottom)
                && !(rightHandSide instanceof Bottom)
                && leftHandSide.hashCode() == rightHandSide.hashCode()
                && leftHandSide.equals(rightHandSide);
    }

    public boolean isFalse() {
        return global.equalityOps.isFalse(this);
    }

    /**
     * Specifies whether this equality can be further decomposed by the
     * unification algorithm of {@code SymbolicUnifier}.
     */
    public boolean isSimplifiableByCurrentAlgorithm() {
        return !leftHandSide.isSymbolic() && !rightHandSide.isSymbolic()
                && (!(leftHandSide instanceof BuiltinMap) && !(rightHandSide instanceof BuiltinMap))
                && !(leftHandSide instanceof BuiltinList) && !(rightHandSide instanceof BuiltinList)
                && !(leftHandSide instanceof BuiltinSet) && !(rightHandSide instanceof BuiltinSet)
                || BuiltinMap.isMapUnifiableByCurrentAlgorithm(leftHandSide, rightHandSide)
                || BuiltinSet.isSetUnifiableByCurrentAlgorithm(leftHandSide, rightHandSide);
    }

    public KItem toK() {
        return KItem.of(
                KLabelConstant.of(KLabels.EQUALS_K, global.getDefinition()),
                KList.concatenate(leftHandSide, rightHandSide),
                global);
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
        hashCode = hashCode * Constants.HASH_PRIME + leftHandSide.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + rightHandSide.hashCode();
        return hashCode;
    }

    @Override
    public String toString() {
        return leftHandSide + SEPARATOR + rightHandSide;
    }

    public static class EqualityOperations {

        private final Provider<Definition> definitionProvider;

        public EqualityOperations(Provider<Definition> definitionProvider) {
            this.definitionProvider = definitionProvider;
        }

        /**
         * Checks if a given equality is false.
         *
         * @return {@code true} if this equality is definitely false; otherwise,
         * {@code false}
         */
        public boolean isFalse(Equality equality) {
            Definition definition = definitionProvider.get();
            Term leftHandSide = equality.leftHandSide;
            Term rightHandSide = equality.rightHandSide;

            if (leftHandSide.isGround() && leftHandSide.isNormal()
                    && rightHandSide.isGround() && rightHandSide.isNormal()) {
                return leftHandSide.hashCode() != rightHandSide.hashCode()
                        || !leftHandSide.equals(rightHandSide);
            }

            // TODO(YilongL): why do you want to build a false equality (i.e., determined by SymbolicUnifier) in the first place?
            if (leftHandSide instanceof Bottom || rightHandSide instanceof Bottom) {
                return true;
            }

            // TODO(YilongL): I think occurs check should be handled in SymbolicUnifier instead
            if (leftHandSide instanceof Variable
                    && rightHandSide instanceof org.kframework.backend.java.kil.Collection
                    && !((Variable) leftHandSide).unifyCollection((Collection) rightHandSide)) {
                return true;
            } else if (rightHandSide instanceof Variable
                    && leftHandSide instanceof org.kframework.backend.java.kil.Collection
                    && !((Variable) rightHandSide).unifyCollection((Collection) leftHandSide)) {
                return true;
            }

            if (leftHandSide instanceof BuiltinList && rightHandSide instanceof BuiltinList) {
                if (((BuiltinList) leftHandSide).isEmpty() && IntStream.range(0, ((BuiltinList) rightHandSide).size()).anyMatch(((BuiltinList) rightHandSide)::isElement)) {
                    return true;
                }
                if (((BuiltinList) rightHandSide).isEmpty() && IntStream.range(0, ((BuiltinList) leftHandSide).size()).anyMatch(((BuiltinList) leftHandSide)::isElement)) {
                    return true;
                }
            }

            // TODO(YilongL): handle this in SymbolicUnifier?
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
                boolean unifiable = false;
                // TODO(YilongL): find a better way to deal with the case in partial compilation
                // where this code path is invoked on an unevaluated ground function such that
                // that function could return a smaller sort than the main return sort of the function,
                // for which the two can be unified. e.g.:
                // syntax ThreadId ::= Int | "foo" | "getThreadId" [function]
                // ThreadId:Int ?= getThreadId
                if (leftHandSide instanceof Variable && rightHandSide instanceof KItem
                        && !((KItem) rightHandSide).isEvaluable()) {
                    for (Sort sort : ((KItem) rightHandSide).possibleSorts()) {
                        unifiable = unifiable || definition.subsorts().isSubsortedEq(leftHandSide.sort(), sort);
                    }
                    if (!unifiable) {
                        return true;
                    }
                } else if (rightHandSide instanceof Variable && leftHandSide instanceof KItem
                        && !((KItem) leftHandSide).isEvaluable()) {
                    for (Sort sort : ((KItem) leftHandSide).possibleSorts()) {
                        unifiable = unifiable || definition.subsorts().isSubsortedEq(rightHandSide.sort(), sort);
                    }
                    if (!unifiable) {
                        return true;
                    }
                }

                return !definition.subsorts().hasCommonSubsort(leftHandSide.sort(), rightHandSide.sort());
            }
        }
    }

}
