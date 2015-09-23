package org.kframework.backend.java.symbolic;

import com.google.common.collect.Sets;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.RuleAutomatonDisjunction;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.builtin.KLabels;
import org.kframework.kore.Assoc;

import static org.kframework.Collections.*;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.commons.lang3.tuple.Pair;


public class FastRuleMatcher {

    private ConjunctiveFormula[] substitutions;
    private BitSet empty;

    private final TermContext context;

    private final KLabelConstant kSeqLabel;
    private final KLabelConstant kDotLabel;
    private final KItem kDot;

    public FastRuleMatcher(TermContext context) {
        this.context = context;
        kSeqLabel = KLabelConstant.of(KLabels.KSEQ, context.definition());
        kDotLabel = KLabelConstant.of(KLabels.DOTK, context.definition());
        kDot = KItem.of(kDotLabel, KList.concatenate(), context);
    }

    public List<Pair<Substitution<Variable, Term>, Integer>> mainMatch(Term subject, Term pattern, BitSet ruleMask) {
        SymbolicRewriter.matchStopwatch.start();
        assert subject.isGround();

        substitutions = new ConjunctiveFormula[ruleMask.length()];
        ruleMask.stream().forEach(i -> substitutions[i] = ConjunctiveFormula.of(context));
        empty = new BitSet(ruleMask.size());

        BitSet theMatchingRules = match(subject, pattern, ruleMask);

        List<Pair<Substitution<Variable, Term>, Integer>> theResult = new ArrayList<>();

        for (int i = theMatchingRules.nextSetBit(0); i >= 0; i = theMatchingRules.nextSetBit(i + 1)) {
            theResult.add(Pair.of(substitutions[i].substitution(), i));
        }

        SymbolicRewriter.matchStopwatch.stop();
        return theResult;
    }

    private BitSet match(Term subject, Term pattern, BitSet ruleMask) {
        assert !ruleMask.isEmpty();
        if (pattern instanceof RuleAutomatonDisjunction) {
            BitSet returnSet = new BitSet(ruleMask.size());
            RuleAutomatonDisjunction automatonDisjunction = (RuleAutomatonDisjunction) pattern;

            Set<Pair<Variable, BitSet>> pairs = automatonDisjunction.variableDisjunctions().get(subject.sort());
            for (Pair<Variable, BitSet> p : pairs) {
                BitSet localRuleMask = ((BitSet) ruleMask.clone());
                localRuleMask.and(p.getRight());
                if (!localRuleMask.isEmpty()) {
                    returnSet.or(add(p.getLeft(), subject, localRuleMask));
                }
            }

            if (!(subject instanceof KItem && ((KItem) subject).kLabel() == kSeqLabel)) {
                Pair<KItem, BitSet> pSeq = automatonDisjunction.kItemDisjunctions().get(kSeqLabel);
                if (pSeq != null) {
                    BitSet localRuleMaskSeq = ((BitSet) ruleMask.clone());
                    localRuleMaskSeq.and(pSeq.getRight());
                    if (!localRuleMaskSeq.isEmpty()) {
                        localRuleMaskSeq = match(subject, pSeq.getLeft(), localRuleMaskSeq);
                    }
                    returnSet.or(localRuleMaskSeq);
                }
            }

            if (subject instanceof KItem) {
                Pair<KItem, BitSet> p = automatonDisjunction.kItemDisjunctions().get((KLabelConstant) ((KItem) subject).kLabel());
                if (p != null) {
                    BitSet localRuleMask = ((BitSet) ruleMask.clone());
                    localRuleMask.and(p.getRight());
                    if (!localRuleMask.isEmpty()) {
                        localRuleMask = match(subject, p.getLeft(), localRuleMask);
                    }
                    returnSet.or(localRuleMask);
                }
            } else if (subject instanceof Token) {
                Pair<Token, BitSet> p = automatonDisjunction.tokenDisjunctions().get((Token) subject);
                if (p != null) {
                    BitSet localRuleMask = ((BitSet) ruleMask.clone());
                    localRuleMask.and(p.getRight());
                    returnSet.or(localRuleMask);
                }
            }

            return returnSet;
        }

        // normalize KSeq representations
        if (isKSeq(subject) || isKSeq(pattern)) {
            subject = getCanonicalKSeq(subject);
//            pattern = getCanonicalKSeq(pattern);

            if (isKSeq(subject)) {
                pattern = upKSeq(pattern);
            }
            if (isKSeq(pattern)) {
                subject = upKSeq(subject);
            }
        }

        if (pattern instanceof Variable) {
            return add((Variable) pattern, subject, ruleMask);
        }

        if (subject instanceof KItem && pattern instanceof KItem) {
            KLabelConstant subjectKLabel = (KLabelConstant) ((KItem) subject).kLabel();
            KList subjectKList = (KList) ((KItem) subject).kList();
            KLabelConstant patternKLabel = (KLabelConstant) ((KItem) pattern).kLabel();
            KList patternKList = (KList) ((KItem) pattern).kList();

            if (subjectKLabel != patternKLabel) {
                return empty;
            }

            assert subjectKList.size() == patternKList.size();
            int size = subjectKList.size();
            for (int i = 0; i < size; ++i) {
                ruleMask = match(subjectKList.get(i), patternKList.get(i), ruleMask);
                if (ruleMask.isEmpty()) {
                    return ruleMask;
                }
            }
            return ruleMask;
        } else if (subject instanceof Token && pattern instanceof Token) {
            // TODO: make tokens unique?
            return subject.equals(pattern) ? ruleMask : empty;
        } else {
            throw new AssertionError("unexpected class at matching");
        }
    }

    private BitSet add(Variable variable, Term term, BitSet ruleMask) {
        if (variable.equals(term)) {
            return ruleMask;
        }

        if (!context.definition().subsorts().isSubsortedEq(variable.sort(), term.sort())) {
            return empty;
        }

        BitSet nonConflictualBitset = new BitSet();
        for (int i = ruleMask.nextSetBit(0); i >= 0; i = ruleMask.nextSetBit(i + 1)) {
            substitutions[i] = substitutions[i].unsafeAddVariableBinding(variable, term);
            if (!substitutions[i].isFalse()) {
                nonConflictualBitset.set(i);
            }
        }

        return nonConflictualBitset;
    }


    private static boolean isKSeq(Term term) {
        return term instanceof KItem && ((KItem) term).kLabel().toString().equals(KLabels.KSEQ);
    }

    private static boolean isKSeqVar(Term term) {
        return term instanceof Variable && term.sort().equals(Sort.KSEQUENCE);
    }

    private Term upKSeq(Term otherTerm) {
        if (!isKSeq(otherTerm) && !isKSeqVar(otherTerm))
            otherTerm = KItem.of(kSeqLabel, KList.concatenate(otherTerm, kDot), context);
        return otherTerm;
    }

    private Term getCanonicalKSeq(Term term) {
        return stream(Assoc.flatten(kSeqLabel, Seq(term), kDotLabel).reverse())
                .map(Term.class::cast)
                .reduce((a, b) -> KItem.of(kSeqLabel, KList.concatenate(b, a), context))
                .orElse(kDot);
    }

}
