// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.MapDifference;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemLog;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.RewriteEngineUtils;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * @author YilongL
 */
public class PatternMatcher extends AbstractUnifier {

    /**
     * Represents the substitution after the pattern matching.
     */
    /**
     * Represents a conjunction of multiple collections of substitutions; each
     * collection is a disjunction of substitutions created by some AC-matching
     * between two cell collections. For example:
     * <pre>
     *   Matching pattern {@code <thread> T </thread> <class> C </class> <store> S </store>} against
     *   subject
     *   {@code
     *     <threads>
     *       <thread> t1 </thread>
     *       <thread> t2 </thread>
     *     </threads>
     *     <classes>
     *       <class> c1 </class>
     *       <class> c2 </class>
     *     </classes>
     *     <store> s <store>}
     *   will result in this field being ``(T = t1 \/ T = t2) /\ (C = c1 \/ C = c2)''.
     *   And ``S = s'' is stored in {@link PatternMatcher#fSubstitution}.
     * </pre>
     */
    private ConjunctiveFormula fSubstitution;

    private final boolean matchOnFunctionSymbol;
    /**
     * True if the subject and the pattern have disjoint variables.
     */
    private final boolean disjointVariables;

    private final GlobalContext global;

    public Substitution<Variable, Term> substitution() {
        assert fSubstitution.isSubstitution();
        return fSubstitution.substitution();
    }

    public List<Substitution<Variable, Term>> substitutions() {
        return fSubstitution.getDisjunctiveNormalForm().conjunctions().stream()
                .map(c -> c.simplify(termContext))
                .filter(c -> !c.isFalse())
                .map(ConjunctiveFormula::substitution)
                .collect(Collectors.toList());
    }

    public ConjunctiveFormula rawSubstitution() {
        return fSubstitution;
    }

    /**
     * Checks if the subject term matches the pattern.
     *
     * @param subject
     *            the subject term
     * @param pattern
     *            the pattern
     * @param context
     *            the term context
     * @return {@code true} if the two terms can be matched; otherwise,
     *         {@code false}
     */
    public static boolean matchable(Term subject, Term pattern, TermContext context) {
        return new PatternMatcher(false, false, context).patternMatch(subject, pattern);
    }

    /**
     * Matches a subject term against a rule. Returns possible instantiations
     * when the rule can be applied for sure (all side-conditions are cleared).
     * Note that, however, an empty list doesn't mean that this rule cannot
     * apply definitely; it is possible that side-conditions are blocked by
     * symbolic argument(s).
     *
     * @param subject
     *            the subject term
     * @param rule
     *            the rule
     * @param context
     *            the term context
     * @param logMsg for logging
     * @param nestingLevel for logging
     * @return a list of possible instantiations of the left-hand side of the
     *         rule (each instantiation is represented as a substitution mapping
     *         variables in the pattern to sub-terms in the subject)
     */
    public static List<Substitution<Variable, Term>> match(Term subject, Rule rule, TermContext context,
                                                           String logMsg, int nestingLevel) {
        PatternMatcher matcher = new PatternMatcher(rule.isFunction() || rule.isLemma(), true, context);

        if (!matcher.patternMatch(subject, rule.leftHandSide())) {
            return Collections.emptyList();
        }

        KItemLog.logEvaluatingConstraints(subject, nestingLevel, rule, context.global(), logMsg);
        return RewriteEngineUtils.evaluateConditions(rule, matcher.substitutions(), context);
    }

    public PatternMatcher(boolean matchOnFunctionSymbol, boolean disjointVariables, TermContext context) {
        super(context);
        this.matchOnFunctionSymbol = matchOnFunctionSymbol;
        this.disjointVariables = disjointVariables;
        this.global = termContext.global();
        this.fSubstitution = ConjunctiveFormula.of(global);
    }

    /**
     * Matches the subject term against the pattern. Returns true if the matching succeeds.
     */
    public boolean patternMatch(Term subject, Term pattern) {
        return patternMatch(subject, pattern, ConjunctiveFormula.of(global));
    }

    /**
     * Matches the subject term against the pattern. Returns true if the matching succeeds.
     */
    public boolean patternMatch(Term subject, Term pattern, ConjunctiveFormula substitution) {
        fSubstitution = substitution;
        addUnificationTask(subject, pattern);
        return unify();
    }

    @Override
    boolean stop(Term subject, Term pattern) {
        /*
         * We make no assumption about whether the subject will be ground in the
         * matching algorithm. As for the pattern, all symbolic terms inside it
         * must be variables (no function KLabels, KItem projections, or
         * data-structure lookup/update).
         */
        if (pattern instanceof Variable) {
            Variable variable = (Variable) pattern;

            /* special case for concrete collections  */
            if (variable instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) variable).match(subject)) {
                fail(variable, subject);
                return true;
            }

            /* add substitution */
            add(subject, variable);
            return true;
        }

        if (subject.isSymbolic() && (!(subject instanceof KItem) || !matchOnFunctionSymbol)) {
            fail(subject, pattern);
            return true;
        }

        return false;
    }

    /**
     * try last-resort matching techniques, such as checking hashCode and equals, which
     * are expensive and we do not want to try every time.
     * @param msg The message to throw in the exception if matching can not be completed.
     */
    private void lastChanceMatching(String msg, Term term, Term otherTerm) {
        if (term.hashCode() == otherTerm.hashCode() && term.equals(otherTerm)) {
        } else if (term.isGround() && otherTerm.isGround()
                && term.isNormal() && otherTerm.isNormal()) {
            fail(term, otherTerm);
        } else {
            throw new UnsupportedOperationException(msg);
        }
    }

    /**
     * Binds a variable in the pattern to a subterm of the subject.
     */
    @Override
    void add(Term term, Term variableTerm) {
        if (!(variableTerm instanceof Variable)) {
            fail(variableTerm, term);
            return;
        }

        Variable variable = (Variable) variableTerm;
        if (variable.equals(term)) {
            return;
        }

        /* retrieve the exact element when the term is some singleton collection */
        if (term.kind() == Kind.K || term.kind() == Kind.KLIST) {
            term = KCollection.downKind(term);
        }

        if (!termContext.definition().subsorts().isSubsortedEq(variable.sort(), term.sort())) {
            fail(variable, term);
        }

        if (disjointVariables) {
            fSubstitution = fSubstitution.unsafeAddVariableBinding(variable, term);
        } else {
            fSubstitution = fSubstitution.add(variable, term).simplify(termContext);
        }
        if (fSubstitution.isFalse()) {
            fail(variable, term);
        }
    }

    @Override
    public void unify(BuiltinList builtinList, BuiltinList patternList) {
        if (matchOnFunctionSymbol) {
            addUnificationTask(builtinList.toKore(), patternList.toKore());
            return;
        }

        if (!patternList.isConcreteCollection()) {
            lastChanceMatching("list matching is only supported when one of the lists is a variable.", builtinList, patternList);
            return;
        }

        if (patternList.concreteSize() != builtinList.concreteSize()) {
            fail(builtinList, patternList);
            return;
        }

        for (int i = 0; i < builtinList.concreteSize(); i++) {
            addUnificationTask(builtinList.get(i), patternList.get(i));
        }
    }

    @Override
    public void unify(BuiltinMap builtinMap, BuiltinMap patternBuiltinMap) {
        if (!patternBuiltinMap.isUnifiableByCurrentAlgorithm()) {
            lastChanceMatching("map matching is only supported when one of the maps is a variable.", builtinMap, patternBuiltinMap);
        }

        if (patternBuiltinMap.collectionVariables().isEmpty()
                && (builtinMap.concreteSize() != patternBuiltinMap.concreteSize()
                || builtinMap.collectionPatterns().size() != patternBuiltinMap.collectionPatterns().size())) {
            fail(builtinMap, patternBuiltinMap);
            return;
        }

        // TODO(AndreiS): implement AC matching/unification
        Set<PartialSubstitution> partialSubstitutions = new HashSet<>();
        partialSubstitutions.add(new PartialSubstitution(
                ImmutableSet.<Term>of(),
                ImmutableMapSubstitution.empty()));

        /* match each entry from the pattern */
        for (Map.Entry<Term, Term> patternEntry : patternBuiltinMap.getEntries().entrySet()) {
            List<PartialSubstitution> stepSubstitutions = new ArrayList<>();
            for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
                PatternMatcher matcher = new PatternMatcher(matchOnFunctionSymbol, disjointVariables, termContext);
                matcher.addUnificationTask(entry.getKey(), patternEntry.getKey());
                matcher.addUnificationTask(entry.getValue(), patternEntry.getValue());
                if (matcher.unify()) {
                    stepSubstitutions.add(new PartialSubstitution(
                            ImmutableSet.of(entry.getKey()),
                            matcher.substitution()));
                }
            }
            partialSubstitutions = getCrossProduct(partialSubstitutions, stepSubstitutions);
        }

        /* match each collection abstraction predicate from the pattern */
        for (KItem patternKItem : patternBuiltinMap.collectionPatterns()) {
            List<PartialSubstitution> stepSubstitutions = new ArrayList<>();
            for (KItem kItem : builtinMap.collectionPatterns()) {
                if (kItem.kLabel().equals(patternKItem.kLabel())) {
                    PatternMatcher matcher = new PatternMatcher(matchOnFunctionSymbol, disjointVariables, termContext);
                    if (matcher.patternMatch(kItem.kList(), patternKItem.kList())) {
                        stepSubstitutions.add(new PartialSubstitution(
                                ImmutableSet.<Term>of(kItem),
                                matcher.substitution()));
                    }
                }
            }
            partialSubstitutions = getCrossProduct(partialSubstitutions, stepSubstitutions);
        }

        if (partialSubstitutions.isEmpty()) {
            fail(builtinMap, patternBuiltinMap);
            return;
        }

        List<Substitution<Variable, Term>> substitutions = Lists.newArrayList();
        for (PartialSubstitution ps : partialSubstitutions) {
            Substitution<Variable, Term> substitution = addFrameMatching(
                    builtinMap,
                    patternBuiltinMap,
                    ps,
                    termContext);
            if (substitution != null) {
                substitutions.add(substitution);
            }
        }

        if (substitutions.size() != 1) {
            List<ConjunctiveFormula> conjunctions = substitutions.stream()
                    .map(s -> ConjunctiveFormula.of(s, global))
                    .collect(Collectors.toList());
            fSubstitution = fSubstitution.add(new DisjunctiveFormula(conjunctions, global));
        } else {
            fSubstitution = fSubstitution.addAndSimplify(substitutions.get(0), termContext);
            if (fSubstitution.isFalse()) {
                fail(builtinMap, patternBuiltinMap);
            }
        }
    }

    private static Substitution<Variable, Term> addFrameMatching(
            BuiltinMap builtinMap,
            BuiltinMap patternBuiltinMap,
            PartialSubstitution ps,
            TermContext context) {
        if (!patternBuiltinMap.collectionVariables().isEmpty()) {
            Variable frame = patternBuiltinMap.collectionVariables().iterator().next();
            if (ps.substitution.containsKey(frame)) {
                return null;
            }

            BuiltinMap.Builder builder = BuiltinMap.builder(context.global());
            for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
                if (!ps.matched.contains(entry.getKey())) {
                    builder.put(entry.getKey(), entry.getValue());
                }
            }
            for (Term term : builtinMap.baseTerms()) {
                if (!ps.matched.contains(term)) {
                    builder.concatenate(term);
                }
            }

            return ps.substitution.plus(frame, builder.build());
        } else {
            return ps.substitution;
        }
    }

    private static class PartialSubstitution {
        public final ImmutableSet<Term> matched;
        public final Substitution<Variable, Term> substitution;

        public PartialSubstitution(ImmutableSet<Term> matched, Substitution<Variable, Term> substitution) {
            this.matched = matched;
            this.substitution = substitution;
        }
    }

    private static Set<PartialSubstitution> getCrossProduct(
            Collection<PartialSubstitution> set1,
            Collection<PartialSubstitution> set2) {
        Set<PartialSubstitution> set = new HashSet<>();
        for (PartialSubstitution ps1 : set1) {
            for (PartialSubstitution ps2 : set2) {
                MapDifference<Variable, Term> mapDifference = Maps.difference(
                        ps1.substitution,
                        ps2.substitution);
                // TODO(AndreiS): this fail to match "list(x) list(x)" with "list(null) list(null)"
                if (mapDifference.entriesDiffering().isEmpty()
                        && Sets.intersection(ps1.matched, ps2.matched).isEmpty()) {
                    set.add(new PartialSubstitution(
                            ImmutableSet.<Term>builder()
                                    .addAll(ps1.matched)
                                    .addAll(ps2.matched)
                                    .build(),
                            ps1.substitution.plusAll(mapDifference.entriesOnlyOnRight())));
                }
            }
        }
        return set;
    }

    @Override
    public void unify(BuiltinSet builtinSet, BuiltinSet patternSet) {
        if (!patternSet.isConcreteCollection() || patternSet.concreteSize() > 1) {
            lastChanceMatching("set matching is only supported when one of the sets is a variable.", builtinSet, patternSet);
        }

        if (builtinSet.concreteSize() != patternSet.concreteSize()) {
            fail(builtinSet, patternSet);
            return;
        }

        if (builtinSet.concreteSize() > 0) {
            addUnificationTask(
                    builtinSet.elements().iterator().next(),
                    patternSet.elements().iterator().next());
        }
    }

    @Override
    public void unify(KCollection kCollection, KCollection pattern) {
        assert kCollection.getClass().equals(pattern.getClass());

        int length = pattern.concreteSize();
        if (kCollection.concreteSize() >= length) {
            if (pattern.hasFrame()) {
                add(kCollection.fragment(length), pattern.frame());
                if (failed) {
                    return;
                }
            } else if (kCollection.hasFrame() || kCollection.concreteSize() > length) {
                fail(kCollection, pattern);
                return;
            }

            // kCollection.size() == length
            for (int index = 0; index < length; ++index) {
                addUnificationTask(kCollection.get(index), pattern.get(index));
            }
        } else {
            fail(kCollection, pattern);
        }
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

}
