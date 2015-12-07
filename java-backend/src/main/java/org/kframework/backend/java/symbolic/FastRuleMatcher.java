// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.InnerRHSRewrite;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.RuleAutomatonDisjunction;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.builtin.KLabels;
import org.kframework.kore.KApply;
import org.kframework.utils.BitSet;

import static org.kframework.Collections.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.apache.commons.lang3.tuple.Pair;
import org.apache.commons.lang3.tuple.Triple;

import com.google.common.collect.Sets;

/**
 * A very fast interpreted matching implementation based on merging the rules into a decision-tree like structure.
 * All possible matches are computed in one matching step. The merged term is obtained by putting a Matching Logic
 * disjunction between the bodies of all rules, and then pushing the disjunction down into the term by identifying
 * common structure. Information about the originating rule is retained via a predicate attached to each element of the
 * disjunction.
 */
public class FastRuleMatcher {

    private final ConjunctiveFormula[] constraints;
    private final Map<scala.collection.immutable.List<Integer>, Term>[] rewrites;
    private final int ruleCount;

    /**
     * @return map from AST path to the corresponding rewrite RHS
     */
    public Map<scala.collection.immutable.List<Integer>, Term> getRewrite(int index) {
        return rewrites[index];
    }

    private BitSet empty;

    private final GlobalContext global;

    private final KLabelConstant kSeqLabel;
    private final KItem kDot;

    private final KLabelConstant threadCellBagLabel;
    private final KItem dotThreadCellBag;


    public FastRuleMatcher(GlobalContext global, int ruleCount) {
        this.global = global;
        kSeqLabel = KLabelConstant.of(KLabels.KSEQ, global.getDefinition());
        KLabelConstant kDotLabel = KLabelConstant.of(KLabels.DOTK, global.getDefinition());
        kDot = KItem.of(kDotLabel, KList.concatenate(), global);

        // remove hack when A/AC is properly supported
        threadCellBagLabel = KLabelConstant.of("_ThreadCellBag_", global.getDefinition());
        dotThreadCellBag = KItem.of(KLabelConstant.of(".ThreadCellBag", global.getDefinition()), KList.concatenate(), global);

        this.ruleCount = ruleCount;
        constraints = new ConjunctiveFormula[this.ruleCount];
        rewrites = new Map[this.ruleCount];
    }

    /**
     * Match the subject against the possibly-merged pattern.
     *
     * @return a list of constraints tagged with the Integer identifier of the rule they belong to.
     */
    public List<Triple<ConjunctiveFormula, Boolean, Integer>> mainMatch(
            ConstrainedTerm subject,
            Term pattern,
            BitSet ruleMask,
            boolean computeOne,
            TermContext context) {
        ruleMask.stream().forEach(i -> constraints[i] = ConjunctiveFormula.of(context.global()));
        ruleMask.stream().forEach(i -> rewrites[i] = new HashMap<>());
        empty = BitSet.apply(ruleCount);

        BitSet theMatchingRules = match(subject.term(), pattern, ruleMask, List());

        List<Triple<ConjunctiveFormula, Boolean, Integer>> theResult = new ArrayList<>();

        for (int i = theMatchingRules.nextSetBit(0); i >= 0; i = theMatchingRules.nextSetBit(i + 1)) {
            Rule rule = global.getDefinition().ruleTable.get(i);
            // TODO(YilongL): remove TermContext from the signature once
            // ConstrainedTerm doesn't hold a TermContext anymore
            ConjunctiveFormula patternConstraint = ConjunctiveFormula.of(rule.lookups()).addAll(rule.requires());
            List<Pair<ConjunctiveFormula, Boolean>> ruleResults = ConstrainedTerm.evaluateConstraints(
                    constraints[i],
                    subject.constraint(),
                    patternConstraint,
                    Sets.union(getLeftHandSide(pattern, i).variableSet(), patternConstraint.variableSet()).stream()
                            .filter(v -> !v.name().equals(KOREtoBackendKIL.THE_VARIABLE))
                            .collect(Collectors.toSet()),
                    context);
            for (Pair<ConjunctiveFormula, Boolean> pair : ruleResults) {
                theResult.add(Triple.of(pair.getLeft(), pair.getRight(), i));
                if (computeOne) {
                    return theResult;
                }
            }
//            assert constraints[i].isSubstitution();
//            Substitution<Variable, Term> subst = RewriteEngineUtils.evaluateConditions(rule, constraints[i].substitution(), context);
//            if (subst != null) {
//                theResult.add(Pair.of(subst, i));
//                if (computeOne) {
//                    break;
//                }
//            }
        }
        return theResult;
    }

    private BitSet match(Term subject, Term pattern, BitSet ruleMask, scala.collection.immutable.List<Integer> path) {
        assert !ruleMask.isEmpty();
        if (pattern instanceof RuleAutomatonDisjunction) {
            RuleAutomatonDisjunction automatonDisjunction = (RuleAutomatonDisjunction) pattern;
            BitSet returnSet = BitSet.apply(ruleCount);

            // handle variables in the disjunction
            List<Pair<Variable, BitSet>> pairs = automatonDisjunction.getVariablesForSort(subject.sort());
            for (Pair<Variable, BitSet> p : pairs) {
                if (ruleMask.intersects(p.getRight())) {
                    BitSet localRuleMask = ruleMask.clone();
                    localRuleMask.and(p.getRight());
                    returnSet.or(addSubstitution(p.getLeft(), subject, localRuleMask));
                }
            }

            // try to match the subject as-if it is a singleton kseq, i.e. subject ~> .K
            if (!(subject instanceof KItem && ((KItem) subject).kLabel() == kSeqLabel)) {
                matchInside(subject, ruleMask, path, returnSet, automatonDisjunction.getKItemPatternForKLabel(kSeqLabel));
            }

            // TODO: hack for threads to behave like the kseq above; remove once AC works
            if (!(subject instanceof KItem && ((KItem) subject).kLabel() == threadCellBagLabel) && threadCellBagLabel.ordinal() < automatonDisjunction.getKLabelMaxOrdinal()) {
                matchInside(subject, ruleMask, path, returnSet, automatonDisjunction.getKItemPatternForKLabel(threadCellBagLabel));
            }

            if (subject instanceof KItem) {
                // main match of KItems
                matchInside(subject, ruleMask, path, returnSet, automatonDisjunction.getKItemPatternForKLabel((KLabelConstant) ((KItem) subject).kLabel()));
            } else if (subject instanceof Token) {
                // and matching Tokens
                BitSet rules = automatonDisjunction.tokenDisjunctions.get(subject);
                if (rules != null) {
                    BitSet localRuleMask = ruleMask.clone();
                    localRuleMask.and(rules);
                    returnSet.or(localRuleMask);
                }
            }

            return returnSet;
        }

        // register the RHS of the rewrite we have just encountered, and continue matching on its LHS
        if (pattern instanceof KItem && ((KItem) pattern).kLabel().toString().equals(KLabels.KREWRITE)) {
            KApply rw = (KApply) pattern;
            InnerRHSRewrite innerRHSRewrite = (InnerRHSRewrite) rw.klist().items().get(1);
            BitSet theNewMask = match(subject, (Term) rw.klist().items().get(0), ruleMask, path);

            for (int i = theNewMask.nextSetBit(0); i >= 0; i = theNewMask.nextSetBit(i + 1)) {
                if (innerRHSRewrite.theRHS[i] != null) {
                    rewrites[i].put(path.reverse(), innerRHSRewrite.theRHS[i]);
                }
            }
            return theNewMask;
        }

        // if the pattern is a variable, try to add its binding to the current solution
        if (pattern instanceof Variable) {
            return addSubstitution((Variable) pattern, subject, ruleMask);
        }

        if ((subject.isSymbolic() && !isThreadCellBag(subject) && !subject.equals(dotThreadCellBag))
                || (pattern.isSymbolic() && !isThreadCellBag(pattern) && !pattern.equals(dotThreadCellBag))) {
            return addUnification(subject, pattern, ruleMask, path);
        }

        // normalize KSeq representations
        if (AbstractUnifier.isKSeq(pattern)) {
            subject = upKSeq(subject);
        }

        // TODO: remove the hack below once AC works
        if (isThreadCellBag(pattern) && !subject.sort().equals(Sort.of("ThreadCellBag")) && !isThreadCellBag(subject)) {
            subject = KItem.of(threadCellBagLabel, KList.concatenate(subject, dotThreadCellBag), global);
        }

        if (subject instanceof KItem && pattern instanceof KItem) {
            KItem kitemPattern = (KItem) pattern;

            KLabelConstant subjectKLabel = (KLabelConstant) ((KItem) subject).kLabel();
            KLabelConstant patternKLabel = (KLabelConstant) kitemPattern.kLabel();
            if (subjectKLabel != patternKLabel) {
                return empty;
            }

            KList subjectKList = (KList) ((KItem) subject).kList();
            KList patternKList = (KList) kitemPattern.kList();
            int size = subjectKList.size();

            if (size != patternKList.size()) {
                return empty;
            }

            // main loop matching the klist
            for (int i = 0; i < size; ++i) {
                BitSet childrenDontCareRuleMaskForPosition = kitemPattern.getChildrenDontCareRuleMaskForPosition(i);
                // continue if the pattern under this position only contains "don't care" variables
                if (childrenDontCareRuleMaskForPosition != null && ruleMask.subset(childrenDontCareRuleMaskForPosition)) {
                    continue;
                }

                ruleMask = match(subjectKList.get(i), patternKList.get(i), ruleMask, path.$colon$colon(i));
                if (ruleMask.isEmpty()) {
                    return ruleMask;
                }
            }
            return ruleMask;
        } else if (subject instanceof Token && pattern instanceof Token) {
            // TODO: make tokens unique?
            return subject.equals(pattern) ? ruleMask : empty;
        } else if (subject instanceof KItem && pattern instanceof Token || subject instanceof Token && pattern instanceof KItem) {
            return empty;
        } else {
            throw new AssertionError("unexpected class at matching: " + subject.getClass());
        }
    }

    private void matchInside(Term subject, BitSet ruleMask, scala.collection.immutable.List<Integer> path, BitSet returnSet, Pair<KItem, BitSet> pSeq) {
        if (pSeq != null) {
            if (ruleMask.intersects(pSeq.getRight())) {
                BitSet localRuleMaskSeq = ((BitSet) ruleMask.clone());
                localRuleMaskSeq.and(pSeq.getRight());
                localRuleMaskSeq = match(subject, pSeq.getLeft(), localRuleMaskSeq, path);
                returnSet.or(localRuleMaskSeq);
            }
        }
    }

    private BitSet addSubstitution(Variable variable, Term term, BitSet ruleMask) {
        if (variable.name().equals(KOREtoBackendKIL.THE_VARIABLE)) {
            return ruleMask;
        }

        if (variable.equals(term)) {
            return ruleMask;
        }

        if (!global.getDefinition().subsorts().isSubsortedEq(variable.sort(), term.sort())) {
            return empty;
        }

        for (int i = ruleMask.nextSetBit(0); i >= 0; i = ruleMask.nextSetBit(i + 1)) {
            constraints[i] = constraints[i].add(variable, term).simplify();
            if (constraints[i].isFalse()) {
                ruleMask.clear(i);
            }
        }

        return ruleMask;
    }

    private BitSet addUnification(Term subject, Term pattern, BitSet ruleMask, scala.collection.immutable.List<Integer> path) {
        for (int i = ruleMask.nextSetBit(0); i >= 0; i = ruleMask.nextSetBit(i + 1)) {
            Term leftHandSide = getLeftHandSide(pattern, i);
            Term rightHandSide = getRightHandSide(pattern, i);

            constraints[i] = constraints[i].add(subject, leftHandSide).simplify();
            if (constraints[i].isFalse()) {
                ruleMask.clear(i);
                continue;
            }

            if (rightHandSide != null) {
                rewrites[i].put(path.reverse(), rightHandSide);
            }
        }

        return ruleMask;
    }

    private Term getLeftHandSide(Term pattern, int i) {
        return (Term) pattern.accept(new CopyOnWriteTransformer(null) {
            @Override
            public Term transform(RuleAutomatonDisjunction ruleAutomatonDisjunction) {
                return (Term) ruleAutomatonDisjunction.disjunctions().stream()
                        .filter(p -> p.getRight().get(i))
                        .map(Pair::getLeft)
                        .findAny().get()
                        .accept(this);
            }

            @Override
            public Term transform(KItem kItem) {
                if (!kItem.kLabel().toString().equals(KLabels.KREWRITE)) {
                    return (Term) super.transform(kItem);
                }

                return (Term) ((Term) kItem.klist().items().get(0)).accept(this);
            }
        });
    }

    private Term getRightHandSide(Term pattern, int i) {
        return (Term) pattern.accept(new CopyOnWriteTransformer(null) {
            @Override
            public Term transform(RuleAutomatonDisjunction ruleAutomatonDisjunction) {
                return (Term) ruleAutomatonDisjunction.disjunctions().stream()
                        .filter(p -> p.getRight().get(i))
                        .map(Pair::getLeft)
                        .findAny().get()
                        .accept(this);
            }

            @Override
            public Term transform(KItem kItem) {
                if (!kItem.kLabel().toString().equals(KLabels.KREWRITE)) {
                    return (Term) super.transform(kItem);
                }

                return ((InnerRHSRewrite) kItem.klist().items().get(1)).theRHS[i];
            }
        });
    }

    private Term upKSeq(Term otherTerm) {
        if (!AbstractUnifier.isKSeq(otherTerm) && !AbstractUnifier.isKSeqVar(otherTerm))
            otherTerm = KItem.of(kSeqLabel, KList.concatenate(otherTerm, kDot), global);
        return otherTerm;
    }

    private boolean isThreadCellBag(Term term) {
        return term instanceof KItem && ((KItem) term).kLabel().equals(threadCellBagLabel);
    }

}
