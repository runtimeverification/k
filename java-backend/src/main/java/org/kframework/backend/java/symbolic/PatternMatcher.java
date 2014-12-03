// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.RewriteEngineUtils;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Predicate;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;
import com.google.common.collect.MapDifference;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;


/**
 * @author YilongL
 */
public class PatternMatcher extends AbstractMatcher {

    /**
     * Represents the substitution after the pattern matching.
     */
    private Map<Variable, Term> fSubstitution;

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
    private final Collection<Collection<Map<Variable, Term>>> multiSubstitutions;

    /**
     * Records whether the pattern matcher is currently traversing under a
     * starred cell.
     */
    private boolean isStarNested;

    private final boolean matchOnFunctionSymbol;

    private final TermContext termContext;

    public Map<Variable, Term> substitution() {
        return Collections.unmodifiableMap(fSubstitution);
    }

    public Collection<Collection<Map<Variable, Term>>> multiSubstitutions() {
        return Collections.unmodifiableCollection(multiSubstitutions);
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
        PatternMatcher matcher = new PatternMatcher(false, context);
        try {
            matcher.match(subject, pattern);
        } catch (PatternMatchingFailure e) {
            return false;
        }
        return true;
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
    public static List<Map<Variable, Term>> match(Term subject, Rule rule, TermContext context) {
        PatternMatcher matcher = new PatternMatcher(rule.isFunction() || rule.isLemma(), context);

        if (!matcher.patternMatch(subject, rule.leftHandSide())) {
            return Collections.emptyList();
        }

        return RewriteEngineUtils.evaluateConditions(rule,
                    RewriteEngineUtils.getMultiSubstitutions(matcher.fSubstitution, matcher.multiSubstitutions), context);
    }

    public PatternMatcher(boolean isLemma, TermContext context) {
        this.matchOnFunctionSymbol = isLemma;
        this.termContext = context;
        this.fSubstitution = Maps.newHashMap();
        this.multiSubstitutions = Lists.newArrayList();
    }

    /**
     * Matches the subject term against the pattern.
     *
     * @param subject
     *            the subject term
     * @param pattern
     *            the pattern term
     * @return {@code true} if the matching succeeds; otherwise, {@code false}
     */
    public boolean patternMatch(Term subject, Term pattern) {
        try {
            isStarNested = false;
            match(subject, pattern);
            return true;
        } catch (PatternMatchingFailure e) {
            return false;
        }
    }

    /**
     * Performs generic operations for the matching between the subject term and
     * the pattern term. Term-specific operations are then delegated to the
     * specific {@code match} method by overloading. That is to say, in general,
     * the safe way to match any two terms is to invoke this generic
     * {@code match} method; do not invoke the specialized ones directly unless
     * you know exactly what you are doing.
     */
    @Override
    public void match(Term subject, Term pattern) {
        /*
         * We make no assumption about whether the subject will be ground in the
         * matching algorithm. As for the pattern, all symbolic terms inside it
         * must be variables (no function KLabels, KItem projections, or
         * data-structure lookup/update).
         */

        if (subject.kind().isComputational()) {
            if (!pattern.kind().isComputational()) {
                fail(subject, pattern);
            }

            subject = KCollection.upKind(subject, pattern.kind());
            pattern = KCollection.upKind(pattern, subject.kind());
        }

        if (subject.kind().isStructural()) {
            if (!pattern.kind().isStructural()) {
                fail(subject, pattern);
            }

            Context context = termContext.definition().context();
            subject = CellCollection.upKind(subject, pattern.kind(), context);
            pattern = CellCollection.upKind(pattern, subject.kind(), context);
        }

        if (subject.kind() != pattern.kind()) {
            fail(subject, pattern);
        }

        if (pattern instanceof Variable) {
            Variable variable = (Variable) pattern;

            /* special case for concrete collections  */
            if (variable instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) variable).match(subject)) {
                fail(variable, subject);
            }

            /* add substitution */
            addSubstitution(variable, subject);
        } else if (subject.isSymbolic() && (!(subject instanceof KItem) || !matchOnFunctionSymbol)) {
            fail(subject, pattern);
        } else {
            /* match */
            if (subject.hashCode() != pattern.hashCode() || !subject.equals(pattern)) {
                subject.accept(this, pattern);
            }
        }
    }

    /**
     * Binds a variable in the pattern to a subterm of the subject; calls
     * {@link PatternMatcher#fail(Term, Term)} when the binding fails.
     *
     * @param variable
     *            the variable
     * @param term
     *            the term
     */
    private void addSubstitution(Variable variable, Term term) {
        /* retrieve the exact element when the term is some singleton collection */
        if (term.kind() == Kind.K || term.kind() == Kind.KLIST) {
            term = KCollection.downKind(term);
        }
        if (term.kind() == Kind.CELL_COLLECTION) {
            term = CellCollection.downKind(term);
        }

        if (!termContext.definition().subsorts().isSubsortedEq(variable.sort(), term.sort())) {
            fail(variable, term);
        }

        // TODO(AndreiS): the check below is not sufficient, as the substitution may not be normalized
        /* occurs check */
        if (term.variableSet().contains(variable)) {
            fail(variable, term);
        }

        Term subst = fSubstitution.get(variable);
        if (subst == null) {
            fSubstitution.put(variable, term);
        } else if (!subst.equals(term)) {
            // TODO(AndreiS): the check below is to strong, as the substitution may not be normalized
            // variable = A, term = C, fSubstitution = { A |-> B, B |-> C}
            fail(subst, term);
        }
    }

    /**
     * Binds multiple variables in the pattern to an equal number of subterms of
     * the subject respectively; calls {@link PatternMatcher#fail(Term, Term)}
     * when the binding fails.
     *
     * @param variable
     *            the variable
     * @param data.term
     *            the term
     */
    private void addSubstitution(Map<Variable, Term> substitution) {
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            addSubstitution(entry.getKey(), entry.getValue());
        }
    }

    @Override
    public void match(Bottom bottom, Term pattern) {
        fail(bottom, pattern);
    }

    @Override
    public void match(BuiltinList builtinList, Term pattern) {
        if (!(pattern instanceof BuiltinList)) {
            this.fail(builtinList, pattern);
        }

        if (matchOnFunctionSymbol) {
            builtinList.toK(termContext).accept(this, ((BuiltinList) pattern).toK(termContext));
            // TODO(AndreiS): this ad-hoc evaluation is converting from the KLabel/KList format
            // (used during associative matching) back to builtin representation
            evaluateSubstitution(fSubstitution, termContext);
            return;
        }

        BuiltinList patternList = (BuiltinList) pattern;
        if (!patternList.isConcreteCollection()) {
            throw new UnsupportedOperationException(
                    "list matching is only supported when one of the lists is a variable.");
        }

        if (patternList.concreteSize() != builtinList.concreteSize()) {
            this.fail(builtinList, pattern);
        }

        for (int i = 0; i < builtinList.concreteSize(); i++) {
            match(builtinList.get(i), patternList.get(i));
        }
    }

    @Override
    public void match(BuiltinMap builtinMap, Term pattern) {
        if (!(pattern instanceof BuiltinMap)) {
            this.fail(builtinMap, pattern);
        }
        BuiltinMap patternBuiltinMap = (BuiltinMap) pattern;

        if (!patternBuiltinMap.isUnifiableByCurrentAlgorithm()) {
            throw new UnsupportedOperationException(
                    "map matching is only supported when one of the maps is a variable.");
        }

        if (patternBuiltinMap.collectionVariables().isEmpty()
                && (builtinMap.concreteSize() != patternBuiltinMap.concreteSize()
                || builtinMap.collectionPatterns().size() != patternBuiltinMap.collectionPatterns().size())) {
            this.fail(builtinMap, pattern);
        }

        // TODO(AndreiS): implement AC matching/unification
        /* stash the existing substitution */
        Map<Variable, Term> stashedSubstitution = fSubstitution;

        Set<PartialSubstitution> partialSubstitutions = new HashSet<>();
        partialSubstitutions.add(new PartialSubstitution(
                ImmutableSet.<Term>of(),
                ImmutableMap.<Variable, Term>of()));

        /* match each entry from the pattern */
        for (Map.Entry<Term, Term> patternEntry : patternBuiltinMap.getEntries().entrySet()) {
            List<PartialSubstitution> stepSubstitutions = new ArrayList<>();
            for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
                fSubstitution = new HashMap<>();
                if (patternMatch(entry.getKey(), patternEntry.getKey())
                        && patternMatch(entry.getValue(), patternEntry.getValue())) {
                    stepSubstitutions.add(new PartialSubstitution(
                            ImmutableSet.of(entry.getKey()),
                            ImmutableMap.copyOf(fSubstitution)));
                }
                fSubstitution = null;
            }
            partialSubstitutions = getCrossProduct(partialSubstitutions, stepSubstitutions);
        }

        /* match each collection abstraction predicate from the pattern */
        for (KItem patternKItem : patternBuiltinMap.collectionPatterns()) {
            List<PartialSubstitution> stepSubstitutions = new ArrayList<>();
            for (KItem kItem : builtinMap.collectionPatterns()) {
                fSubstitution = new HashMap<>();
                if (kItem.kLabel().equals(patternKItem.kLabel())) {
                    if (patternMatch(kItem.kList(), patternKItem.kList())) {
                        stepSubstitutions.add(new PartialSubstitution(
                                ImmutableSet.<Term>of(kItem),
                                ImmutableMap.copyOf(fSubstitution)));
                    }
                }
                fSubstitution = null;
            }
            partialSubstitutions = getCrossProduct(partialSubstitutions, stepSubstitutions);
        }

        /* restore the main substitution */
        fSubstitution = stashedSubstitution;

        if (partialSubstitutions.isEmpty()) {
            this.fail(builtinMap, patternBuiltinMap);
        }

        List<Map<Variable, Term>> substitutions = new ArrayList<>();
        for (PartialSubstitution ps : partialSubstitutions) {
            Map<Variable, Term> substitution = addFrameMatching(builtinMap, patternBuiltinMap, ps);
            if (substitution != null) {
                substitutions.add(substitution);
            }
        }

        if (substitutions.size() != 1) {
            multiSubstitutions.add(substitutions);
        } else {
            addSubstitution(substitutions.iterator().next());
        }
    }

    private static Map<Variable, Term> addFrameMatching(
            BuiltinMap builtinMap,
            BuiltinMap patternBuiltinMap,
            PartialSubstitution ps) {
        if (!patternBuiltinMap.collectionVariables().isEmpty()) {
            Variable frame = patternBuiltinMap.collectionVariables().iterator().next();
            if (ps.substitution.containsKey(frame)) {
                return null;
            }

            BuiltinMap.Builder builder = BuiltinMap.builder();
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

            return ImmutableMap.<Variable, Term>builder()
                    .putAll(ps.substitution)
                    .put(frame, builder.build())
                    .build();
        } else {
            return ps.substitution;
        }
    }

    private static class PartialSubstitution {
        public final ImmutableSet<Term> matched;
        public final ImmutableMap<Variable, Term> substitution;

        public PartialSubstitution(ImmutableSet<Term> matched, ImmutableMap<Variable, Term> substitution) {
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
                            ImmutableMap.<Variable, Term>builder()
                                    .putAll(ps1.substitution)
                                    .putAll(mapDifference.entriesOnlyOnRight())
                                    .build()));
                }
            }
        }
        return set;
    }

    @Override
    public void match(BuiltinSet builtinSet, Term pattern) {
        if (!(pattern instanceof BuiltinSet)) {
            this.fail(builtinSet, pattern);
        }

        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    /**
     * Two cells can be unified if and only if they have the same cell label and
     * their contents can be unified.
     */
    @Override
    public void match(Cell cell, Term pattern) {
        if (!(pattern instanceof Cell)) {
            this.fail(cell, pattern);
        }

        Cell<?> otherCell = (Cell<?>) pattern;
        if (!cell.getLabel().equals(otherCell.getLabel())) {
            /*
             * AndreiS: commented out the check below as matching might fail due
             * to KItem < K < KList subsorting:
             * !cell.contentKind().equals(otherCell.contentKind())
             */
            fail(cell, otherCell);
        }

        match(cell.getContent(), otherCell.getContent());
    }

    @Override
    public void match(CellCollection cellCollection, Term pattern) {
        if (!(pattern instanceof CellCollection)) {
            fail(cellCollection, pattern);
        }
        CellCollection otherCellCollection = (CellCollection) pattern;

        Context context = termContext.definition().context();

        if (cellCollection.hasFrame()) {
        // TODO(dwightguth): put this assertion back in once this class is constructed by
        // the injector
//            assert !termContext.definition().context().javaExecutionOption/*s.concreteExecution() :
//                "the subject term should be ground in concrete execution";*/
            if (!otherCellCollection.hasFrame()) {
                fail(cellCollection, otherCellCollection);
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
                match(cellCollection.get(label).iterator().next(),
                        otherCellCollection.get(label).iterator().next());
            }

            Variable frame = cellCollection.hasFrame() ? cellCollection.frame() : null;
            Variable otherFrame = otherCellCollection.hasFrame()? otherCellCollection.frame() : null;

            if (frame != null) {
                if (otherFrame != null && numOfOtherDiffCellLabels == 0) {
                    addSubstitution(otherFrame, cellCollection.removeAll(unifiableCellLabels, context));
                } else {
                    fail(cellCollection, otherCellCollection);
                }
            } else {
                if (numOfOtherDiffCellLabels > 0) {
                    fail(cellCollection, otherCellCollection);
                }
                if (otherFrame == null) {
                    if (numOfDiffCellLabels > 0) {
                        fail(cellCollection, otherCellCollection);
                    }
                } else {
                    addSubstitution(otherFrame, cellCollection.removeAll(unifiableCellLabels, context));
                }
            }
        }
        /* Case 2: both cell collections have explicitly specified starred-cells */
        else {
            assert !isStarNested : "nested cells with multiplicity='*' not supported";
            // TODO(AndreiS): fix this assertions

            if (numOfOtherDiffCellLabels > 0) {
                fail(cellCollection, otherCellCollection);
            }

            ListMultimap<CellLabel, Cell> remainingCellMap = getRemainingCellMap(cellCollection, unifiableCellLabels);

            CellLabel starredCellLabel = null;
            for (CellLabel cellLabel : unifiableCellLabels) {
                if (!termContext.definition().context().getConfigurationStructureMap().get(cellLabel.name()).isStarOrPlus()) {
                    assert cellCollection.get(cellLabel).size() == 1
                            && otherCellCollection.get(cellLabel).size() == 1;
                    match(cellCollection.get(cellLabel).iterator().next(),
                            otherCellCollection.get(cellLabel).iterator().next());
                } else {
                    assert starredCellLabel == null;
                    starredCellLabel = cellLabel;
                }
            }

            if (starredCellLabel == null) {
                // now we have different starred-cells in subject and pattern
                fail(cellCollection, otherCellCollection);
            }

            if (otherCellCollection.hasFrame()) {
                if (cellCollection.get(starredCellLabel).size() < otherCellCollection.get(starredCellLabel).size()) {
                    fail(cellCollection, otherCellCollection);
                }
            } else {
                // now we know otherCellMap.isEmpty() && otherCellCollection is free of frame
                if (cellCollection.hasFrame()
                        || numOfDiffCellLabels > 0
                        || cellCollection.get(starredCellLabel).size() != otherCellCollection
                                .get(starredCellLabel).size()) {
                    fail(cellCollection, otherCellCollection);
                }
            }

            Cell<?>[] cells = cellCollection.get(starredCellLabel).toArray(new Cell[1]);
            Cell<?>[] otherCells = otherCellCollection.get(starredCellLabel).toArray(new Cell[1]);
            Variable frame = cellCollection.hasFrame() ? cellCollection.frame() : null;
            Variable otherFrame = otherCellCollection.hasFrame() ? otherCellCollection.frame() : null;

            // TODO(YilongL): maybe extract the code below that performs searching to a single method
            // temporarily store the current substitution at a safe place before
            // starting to search for multiple substitutions
            Map<Variable, Term> mainSubstitution = fSubstitution;
            isStarNested = true;

            // {@code substitutions} represents all possible substitutions by
            // matching these two cell collections
            Collection<Map<Variable, Term>> substitutions = new ArrayList<Map<Variable, Term>>();

            SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
            // start searching for all possible unifiers
            do {
                // clear the substitution before each attempt of matching
                fSubstitution = new HashMap<Variable, Term>();

                try {
                    for (int i = 0; i < otherCells.length; ++i) {
                        match(cells[generator.getSelection(i)], otherCells[i]);
                    }
                } catch (PatternMatchingFailure e) {
                    continue;
                }

                CellCollection.Builder builder = CellCollection.builder(termContext.definition().context());
                for (int i = 0; i < cells.length; ++i) {
                    if (!generator.isSelected(i)) {
                        builder.add(cells[i]);
                    }
                }
                builder.putAll(remainingCellMap);
                if (frame != null) {
                    builder.concatenate(frame);
                }
                Term cellcoll = builder.build();

                if (otherFrame != null) {
                    addSubstitution(otherFrame, cellcoll);
                } else {
                    // we should've guaranteed that
                    //   cellMap.isEmpty() && cells.length == otherCells.length
                    // when otherFrame == null
                    assert cellcoll.equals(CellCollection.EMPTY);
                }
                substitutions.add(fSubstitution);
            } while (generator.generate());

            // restore the current constraint after searching
            fSubstitution = mainSubstitution;
            isStarNested = false;

            if (substitutions.isEmpty()) {
                fail(cellCollection, otherCellCollection);
            }

            if (substitutions.size() == 1) {
                addSubstitution(substitutions.iterator().next());
            } else {
                multiSubstitutions.add(substitutions);
            }
        }
    }

    private ListMultimap<CellLabel, Cell> getRemainingCellMap(
            CellCollection cellCollection, final ImmutableSet<CellLabel> labelsToRemove) {
        Predicate<CellLabel> notRemoved = new Predicate<CellLabel>() {
            @Override
            public boolean apply(CellLabel cellLabel) {
                return !labelsToRemove.contains(cellLabel);
            }
        };

        return Multimaps.filterKeys(cellCollection.cellMap(), notRemoved);
    }

    @Override
    public void match(KLabelConstant kLabelConstant, Term pattern) {
        if (!kLabelConstant.equals(pattern)) {
            fail(kLabelConstant, pattern);
        }
    }

    @Override
    public void match(KLabelInjection kLabelInjection, Term pattern) {
        if(!(pattern instanceof KLabelInjection)) {
            fail(kLabelInjection, pattern);
        }

        KLabelInjection otherKLabelInjection = (KLabelInjection) pattern;
        match(kLabelInjection.term(), otherKLabelInjection.term());
    }

    @Override
    public void match(Hole hole, Term pattern) {
        if (!hole.equals(pattern)) {
            fail(hole, pattern);
        }
    }

    @Override
    public void match(KItem kItem, Term pattern) {
        if (!(pattern instanceof KItem)) {
            fail(kItem, pattern);
        }

        KItem patternKItem = (KItem) pattern;
        Term kLabel = kItem.kLabel();
        Term kList = kItem.kList();
        match(kLabel, patternKItem.kLabel());
        // TODO(AndreiS): deal with KLabel variables
        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isMetaBinder()) {
                // TODO(AndreiS): deal with non-concrete KLists
                assert kList instanceof KList;
                Multimap<Integer, Integer> binderMap = kLabelConstant.getBinderMap();
                List<Term> terms = new ArrayList<>(((KList) kList).getContents());
                for (Integer boundVarPosition : binderMap.keySet()) {
                    Term boundVars = terms.get(boundVarPosition);
                    Set<Variable> variables = boundVars.variableSet();
                    Map<Variable,Variable> freshSubstitution = Variable.getFreshSubstitution(variables);
                    Term freshBoundVars = boundVars.substituteWithBinders(freshSubstitution, termContext);
                    terms.set(boundVarPosition, freshBoundVars);
                    for (Integer bindingExpPosition : binderMap.get(boundVarPosition)) {
                        Term bindingExp = terms.get(bindingExpPosition-1);
                        Term freshbindingExp = bindingExp.substituteWithBinders(freshSubstitution, termContext);
                        terms.set(bindingExpPosition-1, freshbindingExp);
                    }
                }
                kList = KList.concatenate(terms);
            }
        }
        match(kList, patternKItem.kList());
    }

    @Override
    public void match(Token token, Term pattern) {
        if (!token.equals(pattern)) {
            fail(token, pattern);
        }
    }

    @Override
    public void match(KList kList, Term pattern) {
        if(!(pattern instanceof KList)) {
            fail(kList, pattern);
        }

        KList otherKList = (KList) pattern;
        matchKCollection(kList, otherKList);
    }

    @Override
    public void match(KSequence kSequence, Term pattern) {
        if (!(pattern instanceof KSequence)) {
            this.fail(kSequence, pattern);
        }

        KSequence otherKSequence = (KSequence) pattern;
        matchKCollection(kSequence, otherKSequence);
    }

    private void matchKCollection(KCollection kCollection, KCollection pattern) {
        assert kCollection.getClass().equals(pattern.getClass());

        int length = pattern.concreteSize();
        if (kCollection.concreteSize() >= length) {
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), kCollection.fragment(length));
            } else if (kCollection.hasFrame() || kCollection.concreteSize() > length) {
                fail(kCollection, pattern);
            }

            // kCollection.size() == length
            for (int index = 0; index < length; ++index) {
                match(kCollection.get(index), pattern.get(index));
            }
        } else {
            fail(kCollection, pattern);
        }
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    public static void evaluateSubstitution(Map<Variable, Term> substitution, TermContext context) {
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            entry.setValue(entry.getValue().evaluate(context));
        }
    }

}
