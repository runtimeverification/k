package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.kil.InnerRHSRewrite;
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
import org.kframework.kore.KApply;
import org.kframework.utils.BitSet;

import static org.kframework.Collections.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.lang3.tuple.Pair;


public class FastRuleMatcher {

    private Substitution<Variable, Term>[] substitutions;
    private Map<scala.collection.immutable.List<Integer>, Term>[] rewrites;
    private final int ruleCount;

    public Map<scala.collection.immutable.List<Integer>, Term>[] getRewrites() {
        return rewrites;
    }

    private BitSet empty;

    private final TermContext context;

    private final KLabelConstant kSeqLabel;
    private final KLabelConstant kDotLabel;
    private final KItem kDot;

    private final KLabelConstant threadCellBagLabel;
    private final KItem dotThreadCellBag;


    public FastRuleMatcher(TermContext context, int ruleCount, int variableCount) {
        this.context = context;
        kSeqLabel = KLabelConstant.of(KLabels.KSEQ, context.definition());
        kDotLabel = KLabelConstant.of(KLabels.DOTK, context.definition());
        kDot = KItem.of(kDotLabel, KList.concatenate(), context);

        // remove hack when A/AC is properly supported
        threadCellBagLabel = KLabelConstant.of("_ThreadCellBag_", context.definition());
        dotThreadCellBag = KItem.of(KLabelConstant.of(".ThreadCellBag", context.definition()), KList.concatenate(), context);

        this.ruleCount = ruleCount;
        substitutions = new Substitution[this.ruleCount];
        for (int i = 0; i < this.ruleCount; ++i) {
            //substitutions[i] = new ArraySubstitution(variableCount);
            substitutions[i] = new HashMapSubstitution();
        }

    }

    public List<Pair<Substitution<Variable, Term>, Integer>> mainMatch(Term subject, Term pattern, BitSet ruleMask) {
        SymbolicRewriter.matchStopwatch.start();
        assert subject.isGround();

        ruleMask.stream().forEach(i -> substitutions[i].clear());
        rewrites = new Map[ruleMask.length()];
        ruleMask.stream().forEach(i -> rewrites[i] = new HashMap<>());
        empty = BitSet.apply(ruleCount);

        BitSet theMatchingRules = match(subject, pattern, ruleMask, List());

        List<Pair<Substitution<Variable, Term>, Integer>> theResult = new ArrayList<>();

        for (int i = theMatchingRules.nextSetBit(0); i >= 0; i = theMatchingRules.nextSetBit(i + 1)) {
            theResult.add(Pair.of(substitutions[i], i));
        }

        SymbolicRewriter.matchStopwatch.stop();
        return theResult;
    }

    static long counter1 = 0;
    static long counter2 = 0;
    static long counter3 = 0;
    static long counter4 = 0;
    static long counter5 = 0;
    static long counter6 = 0;

    private BitSet match(Term subject, Term pattern, BitSet ruleMask, scala.collection.immutable.List<Integer> path) {
        assert !ruleMask.isEmpty();
        if (pattern instanceof RuleAutomatonDisjunction) {
            counter1++;
            RuleAutomatonDisjunction automatonDisjunction = (RuleAutomatonDisjunction) pattern;
            //BitSet returnSet = BitSet.apply(ruleCount);
            BitSet returnSet = automatonDisjunction.ruleMask;
            returnSet.clear();

            List<Pair<Variable, BitSet>> pairs = automatonDisjunction.variableDisjunctionsArray[subject.sort().ordinal()];
            for (Pair<Variable, BitSet> p : pairs) {
                counter2++;
                if (ruleMask.intersects(p.getRight())) {
                    BitSet localRuleMask = ruleMask.clone();
                    localRuleMask.and(p.getRight());
                    returnSet.or(add(p.getLeft(), subject, localRuleMask));
                }
            }

            if (!(subject instanceof KItem && ((KItem) subject).kLabel() == kSeqLabel)) {
                counter3++;
                matchInside(subject, ruleMask, path, returnSet, automatonDisjunction.kItemDisjunctionsArray[kSeqLabel.ordinal()]);
            }

            if (!(subject instanceof KItem && ((KItem) subject).kLabel() == threadCellBagLabel)) {
                matchInside(subject, ruleMask, path, returnSet, automatonDisjunction.kItemDisjunctionsArray[threadCellBagLabel.ordinal()]);
            }

            if (subject instanceof KItem) {
                counter4++;
                matchInside(subject, ruleMask, path, returnSet, automatonDisjunction.kItemDisjunctionsArray[((KLabelConstant) ((KItem) subject).kLabel()).ordinal()]);
            } else if (subject instanceof Token) {
                counter5++;
                Pair<Token, BitSet> p = automatonDisjunction.tokenDisjunctions().get((Token) subject);
                if (p != null) {
                    BitSet localRuleMask = ((BitSet) ruleMask.clone());
                    localRuleMask.and(p.getRight());
                    returnSet.or(localRuleMask);
                }
            }

            return returnSet;
        }
        if (pattern instanceof Variable) {
            return add((Variable) pattern, subject, ruleMask);
        }

        if (pattern instanceof KItem && ((KItem) pattern).kLabel().toString().equals(KLabels.KREWRITE)) {
            KApply rw = (KApply) pattern;
            InnerRHSRewrite innerRHSRewrite = (InnerRHSRewrite) rw.klist().items().get(1);
            BitSet theNewMask = match(subject, (Term) rw.klist().items().get(0), ruleMask, path);

            for (int i = theNewMask.nextSetBit(0); i >= 0; i = theNewMask.nextSetBit(i + 1)) {
                if (innerRHSRewrite.theRHS[i] != null) {
                    counter6++;
                    rewrites[i].put(path, innerRHSRewrite.theRHS[i]);
                }
            }
//            for (int i = 0; i < innerRHSRewrite.theRHS.length; i++) {
//                if (innerRHSRewrite.theRHS[i] != null && theNewMask.get(i)) {
//                    counter6++;
//                    rewrites[i].put(path, innerRHSRewrite.theRHS[i]);
//                }
//            }
            return theNewMask;
        }

        // normalize KSeq representations
        if (isKSeq(pattern)) {
            subject = upKSeq(subject);
        }

        if (pattern instanceof KItem && ((KItem) pattern).kLabel().equals(threadCellBagLabel)
                && !subject.sort().equals(Sort.of("ThreadCellBag"))) {
            subject = KItem.of(threadCellBagLabel, KList.concatenate(subject, dotThreadCellBag), context);
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

            for (int i = 0; i < size; ++i) {
                if (kitemPattern.childrenDontCareRuleMask != null && kitemPattern.childrenDontCareRuleMask[i] != null) {
                    if (ruleMask.subset(kitemPattern.childrenDontCareRuleMask[i])) {
                        continue;
                    }
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

    private BitSet add(Variable variable, Term term, BitSet ruleMask) {
        if (variable.name().equals(KOREtoBackendKIL.THE_VARIABLE)) {
            return ruleMask;
        }

        if (variable.equals(term)) {
            return ruleMask;
        }

        for (int i = ruleMask.nextSetBit(0); i >= 0; i = ruleMask.nextSetBit(i + 1)) {
            if (substitutions[i].plus(variable, term) == null) {
                ruleMask.clear(i);
            }
        }

        return ruleMask;
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
        return (Term) stream(Assoc.flatten(kSeqLabel, Seq(term), kDotLabel).reverse())
                .reduce((a, b) -> KItem.of(kSeqLabel, KList.concatenate((Term) b, (Term) a), context))
                .orElse(kDot);
    }

}
