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

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.commons.lang3.tuple.Pair;


public class FastRuleMatcher {

    private Map<Integer, ConjunctiveFormula> substitutions = new HashMap<>();

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

    public List<Pair<Substitution<Variable, Term>, Integer>> mainMatch(Term subject, Term pattern, Set<Integer> ruleMask) {
        assert subject.isGround();

        substitutions.clear();
        ruleMask.stream().forEach(i -> substitutions.put(i, ConjunctiveFormula.of(context)));

        return match(subject, pattern, ruleMask).stream()
                .map(i -> Pair.of(substitutions.get(i).substitution(), i))
                .collect(Collectors.toList());
    }

    private Set<Integer> match(Term subject, Term pattern, Set<Integer> ruleMask) {
        assert !ruleMask.isEmpty();
        if (pattern instanceof RuleAutomatonDisjunction) {
            Set<Integer> returnSet = Collections.emptySet();
            RuleAutomatonDisjunction automatonDisjunction = (RuleAutomatonDisjunction) pattern;

            for (Pair<Variable, Set<Integer>> p : automatonDisjunction.variableDisjunctions().get(subject.sort())) {
                Set<Integer> localRuleMask = Sets.intersection(ruleMask, p.getRight());
                if (localRuleMask.isEmpty()) {
                    returnSet = Sets.union(returnSet, add(p.getLeft(), subject, localRuleMask));
                }
            }

            if (subject instanceof KItem) {
                Pair<Term, Set<Integer>> p = automatonDisjunction.kItemDisjunctions().get((KLabelConstant) ((KItem) subject).kLabel());
                Set<Integer> localRuleMask = Sets.intersection(ruleMask, p.getRight());
                if (!localRuleMask.isEmpty()) {
                    localRuleMask = match(subject, p.getLeft(), localRuleMask);
                }
                returnSet = Sets.union(returnSet, localRuleMask);
            } else if (subject instanceof Token) {
                Pair<Token, Set<Integer>> p = automatonDisjunction.tokenDisjunctions().get((Token) subject);
                returnSet = Sets.union(returnSet, Sets.intersection(ruleMask, p.getRight()));
            }

            return returnSet;
        }

        // normalize KSeq representations
        if (isKSeq(subject) || isKSeq(pattern)) {
            subject = getCanonicalKSeq(subject);
            pattern = getCanonicalKSeq(pattern);

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
                return Collections.emptySet();
            }

            assert subjectKList.size() == patternKList.size();
            int size = subjectKList.size();
            for (int i = 0; i < size; ++i) {
                ruleMask = match(subjectKList.get(0), patternKList.get(0), ruleMask);
                if (ruleMask.isEmpty()) {
                    return ruleMask;
                }
            }
            return ruleMask;
        } else if (subject instanceof Token && pattern instanceof Token) {
            // TODO: make tokens unique?
            return subject.equals(pattern) ? ruleMask : Collections.emptySet();
        } else {
            throw new AssertionError("unexpected class at matching");
        }
    }

    private Set<Integer> add(Variable variable, Term term, Set<Integer> ruleMask) {
        if (variable.equals(term)) {
            return ruleMask;
        }

        if (!context.definition().subsorts().isSubsortedEq(variable.sort(), term.sort())) {
            return Collections.emptySet();
        }

        return ruleMask.stream()
                .peek(i -> substitutions.put(i, substitutions.get(i).unsafeAddVariableBinding(variable, term)))
                .filter(i -> !substitutions.get(i).isFalse())
                .collect(Collectors.toSet());
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
