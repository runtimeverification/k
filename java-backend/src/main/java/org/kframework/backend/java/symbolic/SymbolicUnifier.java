// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableListMultimap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multiset;
import com.google.common.collect.Multisets;
import com.google.common.collect.Sets;
import org.kframework.compile.ConfigurationInfo;


/**
 * A unifier modulo theories.
 *
 * @author AndreiS
 */
public class SymbolicUnifier extends AbstractUnifier {

    /**
     * A conjunction of disjunctions of {@code SymbolicConstraint}s created by this unifier.
     */
    private ConjunctiveFormula constraint;

    private final boolean patternFold;

    private final boolean partialSimpl;

    private final GlobalContext global;

    public SymbolicUnifier(TermContext context) {
        this(false, false, context);
    }

    public SymbolicUnifier(boolean patternFold, boolean partialSimpl, TermContext context) {
        super(context);
        this.global = context.global();
        this.constraint = ConjunctiveFormula.of(global);
        this.patternFold = patternFold;
        this.partialSimpl = partialSimpl;
    }

    public ConjunctiveFormula constraint() {
        return constraint;
    }

    /**
     * Unifies two given terms. Returns true if the unification succeeds.
     */
    public boolean symbolicUnify(Term term, Term otherTerm) {
        return symbolicUnify(term, otherTerm, ConjunctiveFormula.of(global));
    }

    /**
     * Unifies two given terms. Returns true if the unification succeeds.
     */
    public boolean symbolicUnify(Term term, Term otherTerm, ConjunctiveFormula constraint) {
        this.constraint = constraint;
        addUnificationTask(term, otherTerm);
        return unify();
    }

    @Override
    boolean stop(Term term, Term otherTerm) {
        if (term.hashCode() == otherTerm.hashCode() && term.equals(otherTerm)) {
            return true;
        } else if (term.isGround() && otherTerm.isGround()
                && term.isNormal() && otherTerm.isNormal()) {
            fail(term, otherTerm);
            return true;
        }

        // TODO(AndreiS): treat Map unification less adhoc
        if (BuiltinMap.isMapUnifiableByCurrentAlgorithm(term, otherTerm)) {
            unifyMapModuloPatternFolding((BuiltinMap) term, (BuiltinMap) otherTerm);
            return true;
        }
        // TODO(YilongL): how should I implement BuiltinList#isUnifiableByCurrentAlgorithm?
        if (BuiltinList.isListUnifiableByCurrentAlgorithm(term, otherTerm)) {
            unifyList((BuiltinList) term, (BuiltinList) otherTerm);
            return true;
        }

        if (BuiltinSet.isSetUnifiableByCurrentAlgorithm(term, otherTerm)) {
            unifySet((BuiltinSet) term, (BuiltinSet) otherTerm);
            return true;
        }

        if (term.isSymbolic() || otherTerm.isSymbolic()) {
            // TODO(YilongL): can we move this adhoc code to another place?
            /* special case for concrete collections  */
            if (term instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) term).unify(otherTerm)) {
                fail(term, otherTerm);
                return true;
            }
            if (otherTerm instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) otherTerm).unify(term)) {
                fail(term, otherTerm);
                return true;
            }

            /* add symbolic constraint */
            add(term, otherTerm);
            // YilongL: not the right time to check the truth value because it
            // may change the equalities
            // if (fConstraint.isFalse()) {
            //  fail();
            // }
            return true;
        }
        return false;
    }

    @Override
    void add(Term left, Term right) {
        constraint = constraint.add(left, right);
    }

    void unifyList(BuiltinList list, BuiltinList otherList) {
        int size = Math.min(list.elementsLeft().size(), otherList.elementsLeft().size());
        for (int i = 0; i < size; i++) {
            addUnificationTask(list.get(i), otherList.get(i));
        }
        List<Term> remainingElementsLeft = list.elementsLeft().subList(size, list.elementsLeft().size());
        List<Term> otherRemainingElementsLeft = otherList.elementsLeft().subList(size, otherList.elementsLeft().size());

        size = Math.min(list.elementsRight().size(), otherList.elementsRight().size());
        for (int i = 1; i <= size; i++) {
            addUnificationTask(list.get(-i), otherList.get(-i));
        }
        List<Term> remainingElementsRight = list.elementsRight().subList(0, list.elementsRight().size() - size);
        List<Term> otherRemainingElementsRight = otherList.elementsRight().subList(0, otherList.elementsRight().size() - size);

        List<Term> remainingBaseTerms = list.baseTerms();
        List<Term> otherRemainingBaseTerms = otherList.baseTerms();
        if (remainingElementsLeft.isEmpty() && otherRemainingElementsLeft.isEmpty()) {
            size = Math.min(remainingBaseTerms.size(), otherRemainingBaseTerms.size());
            int left = 0;
            while (left < size) {
                // TODO(YilongL): is it too naive to just check equality between base terms?
                if (list.getBaseTerm(left).equals(otherList.getBaseTerm(left))) {
                    left++;
                } else {
                    break;
                }
            }

            remainingBaseTerms = remainingBaseTerms.subList(left, remainingBaseTerms.size());
            otherRemainingBaseTerms = otherRemainingBaseTerms.subList(left, otherRemainingBaseTerms.size());
        }
        if (remainingElementsRight.isEmpty() && otherRemainingElementsRight.isEmpty()) {
            size = Math.min(remainingBaseTerms.size(), otherRemainingBaseTerms.size());
            int right = 1;
            while (right <= size) {
                if (list.getBaseTerm(-right).equals(otherList.getBaseTerm(-right))) {
                    right++;
                } else {
                    break;
                }
            }

            remainingBaseTerms = remainingBaseTerms.subList(0, remainingBaseTerms.size() - right + 1);
            otherRemainingBaseTerms = otherRemainingBaseTerms.subList(0, otherRemainingBaseTerms.size() - right + 1);
        }

        if (remainingElementsLeft.isEmpty()
                && remainingBaseTerms.isEmpty()
                && remainingElementsRight.isEmpty()
                && (!otherRemainingElementsLeft.isEmpty() || !otherRemainingElementsRight.isEmpty())) {
            fail(list, otherList);
            return;
        }

        if (otherRemainingElementsLeft.isEmpty()
                && otherRemainingBaseTerms.isEmpty()
                && otherRemainingElementsRight.isEmpty()
                && (!remainingElementsLeft.isEmpty() || !remainingElementsRight.isEmpty())) {
            fail(list, otherList);
            return;
        }

        BuiltinList.Builder builder = BuiltinList.builder(global);
        builder.addItems(remainingElementsLeft);
        builder.concatenate(remainingBaseTerms);
        builder.addItems(remainingElementsRight);
        Term remainingList = builder.build();

        BuiltinList.Builder otherBuilder = BuiltinList.builder(global);
        otherBuilder.addItems(otherRemainingElementsLeft);
        otherBuilder.concatenate(otherRemainingBaseTerms);
        otherBuilder.addItems(otherRemainingElementsRight);
        Term otherRemainingList = otherBuilder.build();

        if (!(remainingList instanceof BuiltinList && ((BuiltinList) remainingList).isEmpty())
                || !(otherRemainingList instanceof BuiltinList && ((BuiltinList) otherRemainingList).isEmpty())) {
            if (remainingList instanceof Variable || otherRemainingList instanceof Variable || partialSimpl) {
                add(remainingList, otherRemainingList);
            } else {
                add(list, otherList);
            }
        }
    }

    void unifySet(BuiltinSet set, BuiltinSet otherSet) {
        assert set.collectionFunctions().isEmpty() && otherSet.collectionFunctions().isEmpty();

        Set<Term> elements = set.elements();
        Set<Term> otherElements = otherSet.elements();
        Set<Term> remainingElements = elements.stream()
                .filter(e -> !otherElements.contains(e)).collect(Collectors.toSet());
        Set<Term> otherRemainingElements = otherElements.stream()
                .filter(e -> !elements.contains(e)).collect(Collectors.toSet());

        Multiset<KItem> patterns = set.collectionPatterns();
        Multiset<KItem> otherPatterns = otherSet.collectionPatterns();
        Set<KItem> unifiedPatterns = new HashSet<>();
        Set<KItem> otherUnifiedPatterns = new HashSet<>();
        List<KItem> remainingPatterns = new ArrayList<>();
        List<KItem> otherRemainingPatterns = new ArrayList<>();
        for (KItem pattern : patterns) {
            for (KItem otherPattern : otherPatterns) {
                if (pattern.getPatternInput().equals(otherPattern.getPatternInput())) {
                    List<Term> patternOutput = pattern.getPatternOutput();
                    List<Term> otherPatternOutput = otherPattern.getPatternOutput();
                    for (int i = 0; i < patternOutput.size(); ++i) {
                        addUnificationTask(patternOutput.get(i), otherPatternOutput.get(i));
                    }
                    unifiedPatterns.add(pattern);
                    otherUnifiedPatterns.add(otherPattern);
                }
            }
        }
        for (KItem pattern : patterns) {
            if (!unifiedPatterns.contains(pattern)) {
                remainingPatterns.add(pattern);
            }
        }
        for (KItem otherPattern : otherPatterns) {
            if (!otherUnifiedPatterns.contains(otherPattern)) {
                otherRemainingPatterns.add(otherPattern);
            }
        }

        Multiset<Variable> variables = set.collectionVariables();
        Multiset<Variable> otherVariables = otherSet.collectionVariables();
        Multiset<Variable> commonVariables = Multisets.intersection(variables, otherVariables);
        Multiset<Variable> remainingVariables = Multisets.difference(variables, commonVariables);
        Multiset<Variable> otherRemainingVariables = Multisets.difference(otherVariables, commonVariables);

        if (remainingElements.isEmpty()
                && remainingPatterns.isEmpty()
                && remainingVariables.isEmpty()
                && !otherRemainingElements.isEmpty()) {
            fail(set, otherSet);
            return;
        }
        if (otherRemainingElements.isEmpty()
                && otherRemainingPatterns.isEmpty()
                && otherRemainingVariables.isEmpty()
                && !remainingElements.isEmpty()) {
            fail(set, otherSet);
            return;
        }

        BuiltinSet.Builder builder = BuiltinSet.builder(global);
        builder.addAll(remainingElements);
        builder.concatenate(remainingPatterns.toArray(new Term[remainingPatterns.size()]));
        builder.concatenate(remainingVariables.toArray(new Term[remainingVariables.size()]));
        Term remainingSet = builder.build();

        BuiltinSet.Builder otherBuilder = BuiltinSet.builder(global);
        otherBuilder.addAll(otherRemainingElements);
        otherBuilder.concatenate(otherRemainingPatterns.toArray(new Term[otherRemainingPatterns.size()]));
        otherBuilder.concatenate(otherRemainingVariables.toArray(new Term[otherRemainingVariables.size()]));
        Term otherRemainingSet = otherBuilder.build();

        if (!(remainingSet instanceof BuiltinSet && ((BuiltinSet) remainingSet).isEmpty())
                || !(otherRemainingSet instanceof BuiltinSet && ((BuiltinSet) otherRemainingSet).isEmpty())) {
            if (remainingSet instanceof Variable || otherRemainingSet instanceof Variable || partialSimpl) {
                // set equality resolved or partial simplification enabled
                add(remainingSet, otherRemainingSet);
            } else {
                /* unable to dissolve the entire map equality; thus, we need to
                 * preserve the original set terms for pattern folding */
                add(set, otherSet);
            }
        }
    }

    void unifyMapModuloPatternFolding(BuiltinMap map, BuiltinMap otherMap) {
        if (!patternFold) {
            unifyMap(map, otherMap);
            return;
        }

        Set<BuiltinMap> foldedMaps = Sets.newLinkedHashSet();
        foldedMaps.add(map);
        Queue<BuiltinMap> queue = new LinkedList<>();
        queue.add(map);
        while (!queue.isEmpty()) {
            BuiltinMap candidate = queue.remove();
            for (Rule rule : global.getDefinition().patternFoldingRules()) {
                for (Substitution<Variable, Term> substitution : PatternMatcher.match(candidate, rule, termContext)) {
                    BuiltinMap result = (BuiltinMap) rule.rightHandSide().substituteAndEvaluate(substitution, termContext);
                    if (foldedMaps.add(result)) {
                        queue.add(result);

                        SymbolicUnifier unifier = new SymbolicUnifier(termContext);
                        if (!unifier.symbolicUnify(result, otherMap)) {
                            continue;
                        }
                        ConjunctiveFormula resultConstraint = unifier.constraint().simplify(termContext);

                        /* since here we have a non-deterministic choice to make, we only make
                         * a choice if it eliminates all map equalities */
                        if (!resultConstraint.hasMapEqualities() && !resultConstraint.isFalse()) {
                            constraint = constraint.add(resultConstraint);
                            return;
                        }
                    }
                }
            }
        }

        /* no folding occurred */
        if (foldedMaps.size() == 1) {
            unifyMap(map, otherMap);
            return;
        }

        /* made no progress */
        add(map, otherMap);
    }

    private void unifyMap(BuiltinMap map, BuiltinMap otherMap) {
        assert map.collectionFunctions().isEmpty() && otherMap.collectionFunctions().isEmpty();

        Map<Term, Term> entries = map.getEntries();
        Map<Term, Term> otherEntries = otherMap.getEntries();
        Set<Term> commonKeys = Sets.intersection(map.getEntries().keySet(), otherEntries.keySet());
        Map<Term, Term> remainingEntries = new HashMap<>();
        Map<Term, Term> otherRemainingEntries = new HashMap<>();
        for (Term key : commonKeys) {
            addUnificationTask(entries.get(key), otherEntries.get(key));
        }
        for (Term key : entries.keySet()) {
            if (!commonKeys.contains(key)) {
                remainingEntries.put(key, entries.get(key));
            }
        }
        for (Term key : otherEntries.keySet()) {
            if (!commonKeys.contains(key)) {
                otherRemainingEntries.put(key, otherEntries.get(key));
            }
        }

        Multiset<KItem> patterns = map.collectionPatterns();
        Multiset<KItem> otherPatterns = otherMap.collectionPatterns();
        Set<KItem> unifiedPatterns = new HashSet<>();
        Set<KItem> otherUnifiedPatterns = new HashSet<>();
        List<KItem> remainingPatterns = new ArrayList<>();
        List<KItem> otherRemainingPatterns = new ArrayList<>();
        for (KItem pattern : patterns) {
            for (KItem otherPattern : otherPatterns) {
                if (pattern.kLabel().equals(otherPattern.kLabel())
                        && pattern.getPatternInput().equals(otherPattern.getPatternInput())) {
                    List<Term> patternOutput = pattern.getPatternOutput();
                    List<Term> otherPatternOutput = otherPattern.getPatternOutput();
                    for (int i = 0; i < patternOutput.size(); ++i) {
                        addUnificationTask(patternOutput.get(i), otherPatternOutput.get(i));
                    }
                    unifiedPatterns.add(pattern);
                    otherUnifiedPatterns.add(otherPattern);
                }
            }
        }
        for (KItem pattern : patterns) {
            if (!unifiedPatterns.contains(pattern)) {
                remainingPatterns.add(pattern);
            }
        }
        for (KItem otherPattern : otherPatterns) {
            if (!otherUnifiedPatterns.contains(otherPattern)) {
                otherRemainingPatterns.add(otherPattern);
            }
        }

        Multiset<Variable> variables = map.collectionVariables();
        Multiset<Variable> otherVariables = otherMap.collectionVariables();
        Multiset<Variable> commonVariables = Multisets.intersection(variables, otherVariables);
        Multiset<Variable> remainingVariables = Multisets.difference(variables, commonVariables);
        Multiset<Variable> otherRemainingVariables = Multisets.difference(otherVariables, commonVariables);

        if (remainingEntries.isEmpty()
                && remainingPatterns.isEmpty()
                && remainingVariables.isEmpty()
                && !otherRemainingEntries.isEmpty()) {
            fail(map, otherMap);
            return;
        }
        if (otherRemainingEntries.isEmpty()
                && otherRemainingPatterns.isEmpty()
                && otherRemainingVariables.isEmpty()
                && !remainingEntries.isEmpty()) {
            fail(map, otherMap);
            return;
        }

        BuiltinMap.Builder builder = BuiltinMap.builder(global);
        builder.putAll(remainingEntries);
        builder.concatenate(remainingPatterns.toArray(new Term[remainingPatterns.size()]));
        builder.concatenate(remainingVariables.toArray(new Term[remainingVariables.size()]));
        Term remainingMap = builder.build();

        BuiltinMap.Builder otherBuilder = BuiltinMap.builder(global);
        otherBuilder.putAll(otherRemainingEntries);
        otherBuilder.concatenate(otherRemainingPatterns.toArray(new Term[otherRemainingPatterns.size()]));
        otherBuilder.concatenate(otherRemainingVariables.toArray(new Term[otherRemainingVariables.size()]));
        Term otherRemainingMap = otherBuilder.build();

        if (!(remainingMap instanceof BuiltinMap && ((BuiltinMap) remainingMap).isEmpty())
                || !(otherRemainingMap instanceof BuiltinMap && ((BuiltinMap) otherRemainingMap).isEmpty())) {
            if (remainingMap instanceof Variable || otherRemainingMap instanceof Variable || partialSimpl) {
                // map equality resolved or partial simplification enabled
                add(remainingMap, otherRemainingMap);
            } else {
                /* unable to dissolve the entire map equality; thus, we need to
                 * preserve the original map terms for pattern folding */
                add(map, otherMap);
            }
        }
    }

    @Override
    public void unify(BuiltinList builtinList, BuiltinList term) {
        throw new UnsupportedOperationException(
                "list matching is only supported when one of the lists is a variable.");
    }

    @Override
    public void unify(BuiltinMap builtinMap, BuiltinMap term) {
        throw new UnsupportedOperationException(
                "map matching is only supported when one of the maps is a variable.");
    }

    @Override
    public void unify(BuiltinSet builtinSet, BuiltinSet term) {
        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    @Override
    public void unify(CellCollection cellCollection, CellCollection otherCellCollection) {
        if (cellCollection.hasMultiplicityCell() && !otherCellCollection.hasMultiplicityCell()) {
            /* swap the two specified cell collections in order to reduce to the case 1 below */
            unify(otherCellCollection, cellCollection);
            return;
        }

//        /*
//         * YilongL: I would like to further assert that the configuration
//         * structure of the subject term should be concrete. However, I am not
//         * sure if this is too strong.
//         */
//        assert !(cellCollection.hasFrame() && otherCellCollection.hasFrame());

        Set<CellLabel> unifiableCellLabels = Sets.intersection(cellCollection.labelSet(), otherCellCollection.labelSet());
        int numOfDiffCellLabels = cellCollection.labelSet().size() - unifiableCellLabels.size();
        int numOfOtherDiffCellLabels = otherCellCollection.labelSet().size() - unifiableCellLabels.size();

        Definition definition = global.getDefinition();

        /*
         * CASE 1: cellCollection has no explicitly specified starred-cell;
         * therefore, no need to worry about AC-unification at all!
         */
        if (!cellCollection.hasMultiplicityCell()) {
            for (CellLabel label : unifiableCellLabels) {
                assert cellCollection.get(label).size() == 1
                        && otherCellCollection.get(label).size() == 1;
                addUnificationTask(cellCollection.get(label).iterator().next().content(),
                        otherCellCollection.get(label).iterator().next().content());
            }

            Variable frame = cellCollection.hasFrame() ? cellCollection.frame() : null;
            Variable otherFrame = otherCellCollection.hasFrame()? otherCellCollection.frame() : null;

            if (frame != null && otherFrame != null && (numOfDiffCellLabels > 0) && (numOfOtherDiffCellLabels > 0)) {
                Variable variable = Variable.getAnonVariable(Sort.BAG);
                add(frame, CellCollection.of(getRemainingCellMap(otherCellCollection, unifiableCellLabels), variable, otherCellCollection.cellSort(), definition));
                add(CellCollection.of(getRemainingCellMap(cellCollection, unifiableCellLabels), variable, cellCollection.cellSort(), definition), otherFrame);
            } else if (frame == null && (numOfOtherDiffCellLabels > 0)
                    || otherFrame == null && (numOfDiffCellLabels > 0)) {
                fail(cellCollection, otherCellCollection);
                return;
            } else if (frame == null && otherFrame == null) {
                assert numOfDiffCellLabels == 0 && numOfOtherDiffCellLabels == 0;
            } else {
                add(CellCollection.of(getRemainingCellMap(cellCollection, unifiableCellLabels),
                            frame, cellCollection.cellSort(), definition),
                    CellCollection.of(getRemainingCellMap(otherCellCollection, unifiableCellLabels),
                            otherFrame, otherCellCollection.cellSort(), definition));
            }
        }
        /* Case 2: both cell collections have explicitly specified starred-cells */
        else {
            // TODO(AndreiS): fix this assertions

            assert !(cellCollection.hasFrame() && otherCellCollection.hasFrame()) :
                "Two cell collections both having starred cells in their explicit contents and frames: " +
                "unable to handle this case at present since it greatly complicates the AC-unification";
            if (cellCollection.hasFrame()) {
                /* swap two cell collections to make sure cellCollection is free of frame */
                CellCollection tmp = cellCollection;
                cellCollection = otherCellCollection;
                otherCellCollection = tmp;
            }

            // from now on, we assume that cellCollection is free of frame
            ListMultimap<CellLabel, CellCollection.Cell> cellMap = getRemainingCellMap(cellCollection, unifiableCellLabels);

            if (numOfOtherDiffCellLabels > 0) {
                fail(cellCollection, otherCellCollection);
                return;
            }

            CellLabel starredCellLabel = null;
            for (CellLabel cellLabel : unifiableCellLabels) {
                if (definition.cellMultiplicity(cellLabel) != ConfigurationInfo.Multiplicity.STAR) {
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
                fail(cellCollection, otherCellCollection);
                return;
            }

            if (cellCollection.concreteSize() < otherCellCollection.concreteSize()
                    || cellCollection.concreteSize() > otherCellCollection.concreteSize()
                    && !otherCellCollection.hasFrame()) {
                fail(cellCollection, otherCellCollection);
                return;
            }

            CellCollection.Cell[] cells = cellCollection.get(starredCellLabel).toArray(new CellCollection.Cell[1]);
            CellCollection.Cell[] otherCells = otherCellCollection.get(starredCellLabel).toArray(new CellCollection.Cell[1]);
            Variable otherFrame = otherCellCollection.hasFrame() ? otherCellCollection.frame() : null;

            // TODO(YilongL): maybe extract the code below that performs searching to a single method
            // temporarily store the current constraint at a safe place before
            // starting to search for multiple unifiers
            List<ConjunctiveFormula> constraints = Lists.newArrayList();

            if (otherCells.length > cells.length) {
                fail(cellCollection, otherCellCollection);
                return;
            }
            SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
            // start searching for all possible unifiers
        label:
            do {
                ConjunctiveFormula nestedConstraint = ConjunctiveFormula.of(global);

                for (int i = 0; i < otherCells.length; ++i) {
                    SymbolicUnifier unifier = new SymbolicUnifier(patternFold, partialSimpl, termContext);
                    unifier.addUnificationTask(
                            cells[generator.getSelection(i)].content(),
                            otherCells[i].content());
                    if (unifier.unify()) {
                        nestedConstraint = nestedConstraint.add(unifier.constraint);
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
                    builder.putAll(cellMap);
                    nestedConstraint = nestedConstraint.add(builder.build(), otherFrame);
                }

                constraints.add(nestedConstraint);
            } while (generator.generate());

            if (constraints.isEmpty()) {
                fail(cellCollection, otherCellCollection);
                return;
            } else if (constraints.size() == 1) {
                this.constraint = this.constraint.add(constraints.get(0));
            } else {
                this.constraint = this.constraint.add(new DisjunctiveFormula(
                        constraints,
                        global));
            }
        }
    }

    private ListMultimap<CellLabel, CellCollection.Cell> getRemainingCellMap(
            CellCollection cellCollection,
            Set<CellLabel> labelsToRemove) {
        ImmutableListMultimap.Builder<CellLabel, CellCollection.Cell> builder = ImmutableListMultimap.builder();
        cellCollection.cells().asMap().entrySet().stream().forEach(e -> {
            if (!labelsToRemove.contains(e.getKey())) {
                builder.putAll(e.getKey(), e.getValue());
            }
        });
        return builder.build();
    }

    @Override
    public void unify(KCollection kCollection, KCollection otherKCollection) {
        assert kCollection.getClass().equals(otherKCollection.getClass());

        int length = Math.min(kCollection.concreteSize(), otherKCollection.concreteSize());
        for(int index = 0; index < length; ++index) {
            addUnificationTask(kCollection.get(index), otherKCollection.get(index));
        }

        if (kCollection.concreteSize() < otherKCollection.concreteSize()) {
            if (!kCollection.hasFrame()) {
                fail(kCollection, otherKCollection);
                return;
            }
            add(kCollection.frame(), otherKCollection.fragment(length));
        } else if (otherKCollection.concreteSize() < kCollection.concreteSize()) {
            if (!otherKCollection.hasFrame()) {
                fail(kCollection, otherKCollection);
                return;
            }
            add(kCollection.fragment(length), otherKCollection.frame());
        } else {
            if (kCollection.hasFrame() && otherKCollection.hasFrame()) {
                add(kCollection.frame(), otherKCollection.frame());
            } else if (kCollection.hasFrame()) {
                add(kCollection.frame(), otherKCollection.fragment(length));
            } else if (otherKCollection.hasFrame()) {
                add(kCollection.fragment(length), otherKCollection.frame());
            }
        }
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

}
