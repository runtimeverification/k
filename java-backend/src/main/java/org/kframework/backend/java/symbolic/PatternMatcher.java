// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.MapDifference;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.RewriteEngineUtils;
import org.kframework.compile.ConfigurationInfo;

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
     * @return a list of possible instantiations of the left-hand side of the
     *         rule (each instantiation is represented as a substitution mapping
     *         variables in the pattern to sub-terms in the subject)
     */
    public static List<Substitution<Variable, Term>> match(Term subject, Rule rule, TermContext context) {
        PatternMatcher matcher = new PatternMatcher(rule.isFunction() || rule.isLemma(), true, context);

        if (!matcher.patternMatch(subject, rule.leftHandSide())) {
            return Collections.emptyList();
        }

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
            addUnificationTask(
                    ((BuiltinList) BuiltinList.concatenate(global, builtinList)).toKore(),
                    ((BuiltinList) BuiltinList.concatenate(global, patternList)).toKore());
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
    public void unify(CellCollection cellCollection, CellCollection otherCellCollection) {
        if (cellCollection.hasFrame()) {
        // TODO(dwightguth): put this assertion back in once this class is constructed by
        // the injector
//            assert !termContext.definition().context().javaExecutionOption/*s.concreteExecution() :
//                "the subject term should be ground in concrete execution";*/
            if (!otherCellCollection.hasFrame()) {
                fail(cellCollection, otherCellCollection);
                return;
            }
        }

        ImmutableSet<CellLabel> unifiableCellLabels = ImmutableSet.copyOf(
                Sets.intersection(cellCollection.labelSet(), otherCellCollection.labelSet()));
        int numOfDiffCellLabels = cellCollection.labelSet().size() - unifiableCellLabels.size();
        int numOfOtherDiffCellLabels = otherCellCollection.labelSet().size() - unifiableCellLabels.size();

        /*
         * Case 1: at least one of the cell collections has no explicitly
         * specified starred-cell; therefore, no need to worry about AC-matching
         * at all!
         */
        if (!cellCollection.hasMultiplicityCell() || !otherCellCollection.hasMultiplicityCell()) {
            for (CellLabel label : unifiableCellLabels) {
                assert cellCollection.get(label).size() == 1
                        && otherCellCollection.get(label).size() == 1;
                addUnificationTask(cellCollection.get(label).iterator().next().content(),
                        otherCellCollection.get(label).iterator().next().content());
            }

            Variable frame = cellCollection.hasFrame() ? cellCollection.frame() : null;
            Variable otherFrame = otherCellCollection.hasFrame()? otherCellCollection.frame() : null;

            if (frame != null) {
                if (otherFrame != null && numOfOtherDiffCellLabels == 0) {
                    add(cellCollection.removeAll(unifiableCellLabels), otherFrame);
                    if (failed) {
                        return;
                    }
                } else {
                    fail(cellCollection, otherCellCollection);
                    return;
                }
            } else {
                if (numOfOtherDiffCellLabels > 0) {
                    fail(cellCollection, otherCellCollection);
                    return;
                }
                if (otherFrame == null) {
                    if (numOfDiffCellLabels > 0) {
                        fail(cellCollection, otherCellCollection);
                        return;
                    }
                } else {
                    add(cellCollection.removeAll(unifiableCellLabels), otherFrame);
                    if (failed) {
                        return;
                    }
                }
            }
        }
        /* Case 2: both cell collections have explicitly specified starred-cells */
        else {
            if (numOfOtherDiffCellLabels > 0) {
                fail(cellCollection, otherCellCollection);
                return;
            }

            ListMultimap<CellLabel, CellCollection.Cell> remainingCellMap = getRemainingCellMap(cellCollection, unifiableCellLabels);

            CellLabel starredCellLabel = null;
            for (CellLabel cellLabel : unifiableCellLabels) {
                if (termContext.definition().cellMultiplicity(cellLabel) != ConfigurationInfo.Multiplicity.STAR) {
                    assert cellCollection.get(cellLabel).size() == 1
                            && otherCellCollection.get(cellLabel).size() == 1;
                    addUnificationTask(cellCollection.get(cellLabel).iterator().next().content(),
                            otherCellCollection.get(cellLabel).iterator().next().content());
                } else {
                    assert starredCellLabel == null;
                    starredCellLabel = cellLabel;
                }
            }

            if (starredCellLabel == null) {
                // now we have different starred-cells in subject and pattern
                fail(cellCollection, otherCellCollection);
                return;
            }

            CellCollection.Cell[] cells = cellCollection.get(starredCellLabel)
                    .toArray(new CellCollection.Cell[1]);
            CellCollection.Cell[] otherCells = otherCellCollection.get(starredCellLabel)
                    .toArray(new CellCollection.Cell[1]);
            if (otherCellCollection.hasFrame()) {
                if (cells.length < otherCells.length) {
                    fail(cellCollection, otherCellCollection);
                    return;
                }
            } else {
                // now we know otherCellMap.isEmpty() && otherCellCollection is free of frame
                if (cellCollection.hasFrame()
                        || numOfDiffCellLabels > 0
                        || cells.length != otherCells.length) {
                    fail(cellCollection, otherCellCollection);
                    return;
                }
            }

            Variable frame = cellCollection.hasFrame() ? cellCollection.frame() : null;
            Variable otherFrame = otherCellCollection.hasFrame() ? otherCellCollection.frame() : null;

            // {@code substitutions} represents all possible substitutions by
            // matching these two cell collections
            List<ConjunctiveFormula> substitutions = Lists.newArrayList();

            SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
            // start searching for all possible unifiers
        label:
            do {
                ConjunctiveFormula nestedSubstitution = ConjunctiveFormula.of(global);

                for (int i = 0; i < otherCells.length; ++i) {
                    PatternMatcher matcher = new PatternMatcher(matchOnFunctionSymbol, disjointVariables, termContext);
                    matcher.addUnificationTask(
                            cells[generator.getSelection(i)].content(),
                            otherCells[i].content());
                    if (matcher.unify()) {
                        nestedSubstitution = nestedSubstitution.addAndSimplify(matcher.fSubstitution, termContext);
                        if (nestedSubstitution.isFalse()) {
                            continue label;
                        }
                    } else {
                        continue label;
                    }
                }

                if (otherFrame != null) {
                    CellCollection.Builder builder = cellCollection.builder();
                    for (int i = 0; i < cells.length; ++i) {
                        if (!generator.isSelected(i)) {
                            builder.add(cells[i]);
                        }
                    }
                    builder.putAll(remainingCellMap);
                    if (frame != null) {
                        builder.concatenate(frame);
                    }
                    nestedSubstitution = nestedSubstitution.add(builder.build(), otherFrame).simplify(termContext);
                    if (nestedSubstitution.isFalse()) {
                        continue label;
                    }
                }

                substitutions.add(nestedSubstitution);
            } while (generator.generate());

            if (substitutions.isEmpty()) {
                fail(cellCollection, otherCellCollection);
                return;
            } else if (substitutions.size() == 1) {
                fSubstitution = fSubstitution.addAndSimplify(substitutions.get(0), termContext);
                if (fSubstitution.isFalse()) {
                    fail(cellCollection, otherCellCollection);
                    return;
                }
            } else {
                fSubstitution = fSubstitution.add(new DisjunctiveFormula(
                        substitutions,
                        global));
            }
        }
    }

    private ListMultimap<CellLabel, CellCollection.Cell> getRemainingCellMap(
            CellCollection cellCollection, final ImmutableSet<CellLabel> labelsToRemove) {
        return Multimaps.filterKeys(cellCollection.cells(), l -> !labelsToRemove.contains(l));
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
