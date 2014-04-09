package org.kframework.backend.java.symbolic;


import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimap;


/**
 * @author YilongL
 */
public class PatternMatcher extends AbstractMatcher {

    /**
     * Represents the substitution after the pattern matching.
     */
    private Map<Variable, Term> fSubstitution = new HashMap<Variable, Term>();
    
    /**
     * Represents a conjunction of multiple collections of substitutions; each
     * collection is a disjunction of substitutions created by some AC-matching
     * between two cell collections.
     */
    private final Collection<Collection<Map<Variable, Term>>> multiSubstitutions;
    
    /**
     * Records whether the pattern matcher is currently traversing under a
     * starred cell.
     */
    private boolean isStarNested;
    
    private final TermContext termContext;
    
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
        PatternMatcher matcher = new PatternMatcher(context);
        try {
            matcher.match(subject, pattern);
        } catch (PatternMatchingFailure e) {
            return false;
        }
        return true;
    }
    
    /**
     * Matches a subject term against a rule.
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
    public static List<Map<Variable, Term>> patternMatch(Term subject, Rule rule, TermContext context) {
        PatternMatcher matcher = new PatternMatcher(context);
        if (!matcher.patternMatch(subject, rule.leftHandSide())) {
            return Collections.emptyList();
        }

        /* handle fresh variables, data structure lookups, and side conditions */
        List<Map<Variable, Term>> substitutions = new ArrayList<Map<Variable, Term>>();
        label: 
        for (Map<Variable, Term> subst : getMultiSubstitutions(matcher)) {
            /* add bindings for fresh variables used in the rule */
            for (Variable variable : rule.freshVariables()) {
                subst.put(variable, IntToken.fresh());
            }
            
            /* evaluate data structure lookups and add bindings for them */
            List<Map<Variable, Term>> multiSubsts = new ArrayList<>(Collections.singletonList(subst));
            for (UninterpretedConstraint.Equality equality : rule.lookups().equalities()) {
                Term lookup = equality.leftHandSide() instanceof DataStructureLookup ? 
                        equality.leftHandSide() : equality.rightHandSide();
                Term nonLookup = equality.leftHandSide() == lookup ? 
                        equality.rightHandSide() : equality.leftHandSide();
                assert lookup instanceof DataStructureLookup : 
                    "one side of the equality should be an instance of DataStructureLookup";
                
                Term evaluatedLookup = lookup.substituteAndEvaluate(subst, context);
                if (nonLookup instanceof Variable) {
                    Variable variable = (Variable) nonLookup;
                    if (checkOrderedSortedCondition(variable, evaluatedLookup, context)) {
                        for (Map<Variable, Term> subst2 : multiSubsts) {
                            subst2.put(variable, evaluatedLookup);
                        }
                    } else {
                        continue label;
                    }
                } else {
                    // the non-lookup term is not a variable and thus requires further pattern matching
                    PatternMatcher lookupMatcher = new PatternMatcher(context);
                    if (lookupMatcher.patternMatch(evaluatedLookup, nonLookup)) {
                        List<Map<Variable, Term>> product = new ArrayList<Map<Variable, Term>>();
                        // it's possible that multiple substitutions are possible from the pattern matching above
                        for (Map<Variable, Term> subst1 : PatternMatcher.getMultiSubstitutions(lookupMatcher)) {
                            for (Map<Variable, Term> subst2 : multiSubsts) {
                                Map<Variable, Term> composedSubst = composeSubstitution(subst1, subst2);
                                if (composedSubst != null) {
                                    product.add(composedSubst);
                                }
                            }
                        }
                        if (product.isEmpty()) {
                            continue label;
                        } else {
                            multiSubsts = product;
                        }
                    } else {
                        continue label;
                    }
                }
            }
            
            /* evaluate side conditions */
            Iterator<Map<Variable, Term>> iter = multiSubsts.iterator();
            while (iter.hasNext()) {
                Map<Variable, Term> nextSubst = iter.next();
                for (Term require : rule.requires()) {
                    if (!require.substituteAndEvaluate(nextSubst, context).equals(BoolToken.TRUE)) {
                        iter.remove();
                        break;
                    }
                }
            }
            
            substitutions.addAll(multiSubsts);
        }
        
        return substitutions;
    }
    
    /**
     * Private helper method which constructs all possible variable bindings of
     * the pattern term to match the subject term, given the pattern matcher
     * object that is used to perform the matching.
     * 
     * @param matcher
     *            the pattern matcher
     * @return all possible substitutions of the pattern term to match the
     *         subject term
     */
    private static List<Map<Variable, Term>> getMultiSubstitutions(PatternMatcher matcher) {
        if (!matcher.multiSubstitutions.isEmpty()) {
            assert matcher.multiSubstitutions.size() <= 2;
            
            List<Map<Variable, Term>> result = new ArrayList<Map<Variable, Term>>();
            Iterator<Collection<Map<Variable, Term>>> iterator = matcher.multiSubstitutions.iterator();
            if (matcher.multiSubstitutions.size() == 1) {
                for (Map<Variable, Term> subst : iterator.next()) {
                    Map<Variable, Term> composedSubst = composeSubstitution(matcher.fSubstitution, subst);
                    if (composedSubst != null) {
                        result.add(composedSubst);
                    }
                }
            } else {
                Collection<Map<Variable, Term>> substitutions = iterator.next();
                Collection<Map<Variable, Term>> otherSubstitutions = iterator.next();
                for (Map<Variable, Term> subst1 : substitutions) {
                    for (Map<Variable, Term> subst2 : otherSubstitutions) {
                        Map<Variable, Term> composedSubst = composeSubstitution(matcher.fSubstitution, subst1);
                        if (composedSubst != null) {
                            composedSubst = composeSubstitution(composedSubst, subst2);
                            if (composedSubst != null) {
                                result.add(composedSubst);
                            }
                        }
                    }
                }
            }
            return result;
        } else {
            return Collections.singletonList(matcher.fSubstitution);
        }
    }
    
    /**
     * Composes two specified substitutions.
     * 
     * @param subst1
     *            the first substitution
     * @param subst2
     *            the second substitution
     * @return the composed substitution on success; otherwise, {@code null}
     */
    private static Map<Variable, Term> composeSubstitution(Map<Variable, Term> subst1, Map<Variable, Term> subst2) {
        Map<Variable, Term> result = new HashMap<Variable, Term>(subst1);
        for (Map.Entry<Variable, Term> entry : subst2.entrySet()) {
            Variable variable = entry.getKey();
            Term term = entry.getValue();
            Term otherTerm = result.get(variable);
            if (otherTerm == null) {
                result.put(variable, term);
            } else if (!otherTerm.equals(term)) {
                return null;
            }
        }
        return result;
    }

    private PatternMatcher(TermContext context) {
        this.termContext = context;
        multiSubstitutions = new ArrayList<Collection<Map<Variable, Term>>>();
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
    private boolean patternMatch(Term subject, Term pattern) {
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
        if (subject.kind().isComputational()) {
            assert pattern.kind().isComputational();

            subject = KCollection.upKind(subject, pattern.kind());
            pattern = KCollection.upKind(pattern, subject.kind());
        }

        if (subject.kind() == Kind.CELL || subject.kind() == Kind.CELL_COLLECTION) {
            Context context = termContext.definition().context();
            subject = CellCollection.upKind(subject, pattern.kind(), context);
            pattern = CellCollection.upKind(pattern, subject.kind(), context);
        }
        
        // TODO(YilongL): may need to replace the following assertion to the
        // method fail() in the future because it crashes the Java rewrite
        // engine instead of just failing the pattern matching process
        assert subject.kind() == pattern.kind():
               "kind mismatch between " + subject + " (" + subject.kind() + ")"
               + " and " + pattern + " (" + pattern.kind() + ")";

        if (pattern.isSymbolic()) {
            assert pattern instanceof Variable;
            Variable variable = (Variable) pattern;

            /* special case for concrete collections  */
            if (variable instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) variable).matchConcreteSize(subject)) {
                fail(variable, subject);
            }

            /* add substitution */
            addSubstitution(variable, subject);
        } else {
            /* match */
            if (!subject.equals(pattern)) {
                subject.accept(this, pattern);
            }
        }
    }
    
    /**
     * Private helper method that checks if a specified variable binding
     * satisfies the ordered-sorted pattern matching condition; namely, the sort
     * of the term must be subsorted to the sort of the variable.
     * 
     * @param variable
     *            the variable to be bound
     * @param term
     *            the term to be bound to
     * @param termContext 
     * @return {@code true} if the variable can be bound to the term
     *         successfully; otherwise, {@code false}
     */
    private static boolean checkOrderedSortedCondition(Variable variable, Term term, TermContext termContext) {
        return termContext.definition().context().isSubsortedEq(variable.sort(), term.sort());
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
        if (!checkOrderedSortedCondition(variable, term, termContext)) {
            fail(variable, term);
        }
        
        Term subst = fSubstitution.get(variable);
        if (subst == null) {
            fSubstitution.put(variable, term);
        } else if (!subst.equals(term)) {
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
     * @param term
     *            the term
     */
    private void addSubstitution(Map<Variable, Term> substitution) {
        for (Map.Entry<Variable, Term> entry : substitution.entrySet()) {
            addSubstitution(entry.getKey(), entry.getValue());
        }
    }

    @Override
    public void match(BuiltinList builtinList, Term pattern) {
        assert !(pattern instanceof Variable);
        
        if (!(pattern instanceof BuiltinList)) {
            this.fail(builtinList, pattern);
        }
        
        throw new UnsupportedOperationException(
                "list matching is only supported when one of the lists is a variable.");
    }

    @Override
    public void match(BuiltinMap builtinMap, Term pattern) {
        assert !(pattern instanceof Variable);

        if (!(pattern instanceof BuiltinMap)) {
            this.fail(builtinMap, pattern);
        }

        throw new UnsupportedOperationException(
                "map matching is only supported when one of the maps is a variable.");
    }

    @Override
    public void match(BuiltinSet builtinSet, Term pattern) {
        assert !(pattern instanceof Variable);

        if (!(pattern instanceof BuiltinSet)) {
            this.fail(builtinSet, pattern);
        }

        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    @Override
    public void match(BuiltinMgu builtinMgu, Term pattern) {
        assert !(pattern instanceof Variable);
        
        if (!(pattern instanceof BuiltinMgu)) {
            this.fail(builtinMgu, pattern);
        }

        throw new UnsupportedOperationException(
                "Mgu matching is only supported when one of the Mgu's is a variable.");
    }

    /**
     * Two cells can be unified if and only if they have the same cell label and
     * their contents can be unified.
     */
    @Override
    public void match(Cell cell, Term pattern) {
        assert !(pattern instanceof Variable);

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

    /**
     * 
     */
    @Override
    public void match(CellCollection cellCollection, Term pattern) {
        assert !(pattern instanceof Variable);
        
        if (!(pattern instanceof CellCollection)) {
            fail(cellCollection, pattern);
        }
        CellCollection otherCellCollection = (CellCollection) pattern;
        
        assert !cellCollection.hasFrame() : "the subject term should be ground";

        Set<String> unifiableCellLabels = new HashSet<String>(cellCollection.labelSet());
        unifiableCellLabels.retainAll(otherCellCollection.labelSet());

        Context context = termContext.definition().context();
        
        /*
         * Case 1: at least one of the cell collections has no explicitly
         * specified starred-cell; therefore, no need to worry about AC-matching
         * at all!
         */
        if (!cellCollection.hasStar() || !otherCellCollection.hasStar()) {
            for (String label : unifiableCellLabels) {
                assert cellCollection.get(label).size() == 1
                        && otherCellCollection.get(label).size() == 1;
                match(cellCollection.get(label).iterator().next(),
                        otherCellCollection.get(label).iterator().next());
            }

            Multimap<String, Cell> cellMap = ArrayListMultimap.create();
            Multimap<String, Cell> otherCellMap = ArrayListMultimap.create();
            computeDisjointCellMaps(unifiableCellLabels, cellCollection,
                    cellMap, otherCellCollection, otherCellMap);
            
            if (!cellCollection.hasStar()
                    && !addCellCollectionConstraint(
                            cellMap, null,
                            otherCellMap, otherCellCollection.hasFrame() ? otherCellCollection.frame() : null)) {
                fail(cellCollection, otherCellCollection);
            } else if (!otherCellCollection.hasStar()
                    && !addCellCollectionConstraint(
                            otherCellMap, otherCellCollection.hasFrame() ? otherCellCollection.frame() : null, 
                            cellMap, null)) {
                fail(cellCollection, otherCellCollection);
            }
        } 
        /* Case 2: both cell collections have explicitly specified starred-cells */
        else {
            assert !isStarNested : "nested cells with multiplicity='*' not supported";
            // TODO(AndreiS): fix this assertions
        
            // note that cellCollection is free of frame
            Multimap<String, Cell> cellMap = ArrayListMultimap.create();
            Multimap<String, Cell> otherCellMap = ArrayListMultimap.create();
            computeDisjointCellMaps(unifiableCellLabels, cellCollection,
                    cellMap, otherCellCollection, otherCellMap);
            if (!otherCellMap.isEmpty()) {
                fail(cellCollection, otherCellCollection);
            }

            for (Iterator<String> iter = unifiableCellLabels.iterator(); iter.hasNext(); ) {
                String cellLabel = iter.next();
                if (!context.getConfigurationStructureMap().get(cellLabel).isStarOrPlus()) {
                    assert cellCollection.get(cellLabel).size() == 1
                            && otherCellCollection.get(cellLabel).size() == 1;
                    match(cellCollection.get(cellLabel).iterator().next(),
                            otherCellCollection.get(cellLabel).iterator().next());
                    iter.remove();
                }
            }
            
            // YilongL: the assertion here must hold
            if (unifiableCellLabels.isEmpty()) {
                fail(cellCollection, otherCellCollection);
            } else {
                assert unifiableCellLabels.size() == 1;
            }

            if (cellCollection.size() < otherCellCollection.size()
                    || cellCollection.size() > otherCellCollection.size()
                    && !otherCellCollection.hasFrame()) {
                fail(cellCollection, otherCellCollection);
            }

            String label = unifiableCellLabels.iterator().next();
            Cell<?>[] cells = cellCollection.get(label).toArray(new Cell[1]);
            Cell<?>[] otherCells = otherCellCollection.get(label).toArray(new Cell[1]);
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
                        match(cells[generator.selection.get(i)], otherCells[i]);
                    }
                } catch (UnificationFailure e) {
                    continue;
                }

                Multimap<String, Cell> cm = ArrayListMultimap.create();
                for (int i = 0; i < cells.length; ++i) {
                    if (!generator.selected.contains(i)) {
                        cm.put(cells[i].getLabel(), cells[i]);
                    }
                }
                cm.putAll(cellMap);

                if (otherFrame != null) {
                    addSubstitution(otherFrame, new CellCollection(cm, context));
                } else {
                    if (!cm.isEmpty()) {
                        fail(cellCollection, otherCellCollection);
                    }
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

    private void computeDisjointCellMaps(Set<String> unifiableCellLabels,
            CellCollection cellCollection, Multimap<String, Cell> cellMap,
            CellCollection otherCellCollection,
            Multimap<String, Cell> otherCellMap) {
        cellMap.clear();
        for (String label : cellCollection.labelSet()) {
            if (!unifiableCellLabels.contains(label)) {
                cellMap.putAll(label, cellCollection.get(label));
            }
        }

        otherCellMap.clear();
        for (String label : otherCellCollection.labelSet()) {
            if (!unifiableCellLabels.contains(label)) {
                otherCellMap.putAll(label, otherCellCollection.get(label));
            }
        }
    }

    private class SelectionGenerator {

        private final int size;
        private final int coSize;
        public List<Integer> selection;
        public Set<Integer> selected;
        private int index;

        public SelectionGenerator(int size, int coSize) {
            assert size <= coSize;

            this.size = size;
            this.coSize = coSize;
            selection = new ArrayList<Integer>();
            selected = new HashSet<Integer>();
            for (int i = 0; i < size; ++i) {
                selection.add(i);
                selected.add(i);
            }
        }

        private void pop() {
            index = selection.remove(selection.size() - 1);
            selected.remove(index);
            ++index;
        }

        private void push() {
            selection.add(index);
            selected.add(index);
            index = 0;
        }

        public boolean generate() {
            if (selection.isEmpty()) return false;
            pop();
            while (selection.size() != size) {
                if (index == coSize) {
                    if (selection.isEmpty()) {
                        break;
                    } else {
                        pop();
                        continue;
                    }
                }

                if (!selected.contains(index)) {
                    push();
                    continue;
                }

                ++index;
            }

            return !selection.isEmpty();
        }

    }

    /**
     * Private helper method to compute and add constraint(s) between two
     * specialized cell collections. Three preconditions for the arguments: 1)
     * The two specified cell collections shall have no common cell label in
     * their explicit contents; 2) the first cell collection contains no
     * starred-cell in its explicit content; 3) at least one of the cell
     * collections has no frame.
     * 
     * @return true if the constraint addition does not make the matching to
     *         fail
     */
    private boolean addCellCollectionConstraint(
            Multimap<String, Cell> cellMap,
            Variable frame,
            Multimap<String, Cell> otherCellMap,
            Variable otherFrame) {
        for (String cellLabel : cellMap.keySet()) {
            assert !otherCellMap.containsKey(cellLabel);
            assert cellMap.get(cellLabel).size() == 1;
        }
        assert frame == null || otherFrame == null;
        
        Context context = termContext.definition().context();
        
        if (frame != null) {
            // otherFrame == null
            if (!cellMap.isEmpty()) {
                return false;
            }

            addSubstitution(frame, new CellCollection(otherCellMap, context));
        } else {
            // frame == null
            if (!otherCellMap.isEmpty()) {
                return false;
            }

            if (otherFrame == null) {
                if (!cellMap.isEmpty()) {
                    return false;
                }
            } else {
                addSubstitution(otherFrame, new CellCollection(cellMap, context));
            }
        }

        return true;
    }

    @Override
    public void match(KLabelConstant kLabelConstant, Term pattern) {
        assert !(pattern instanceof Variable);
        
        if (!kLabelConstant.equals(pattern)) {
            fail(kLabelConstant, pattern);
        }
    }

    @Override
    public void match(KLabelFreezer kLabelFreezer, Term pattern) {
        assert !(pattern instanceof Variable);

        if(!(pattern instanceof KLabelFreezer)) {
            fail(kLabelFreezer, pattern);
        }

        KLabelFreezer otherKLabelFreezer = (KLabelFreezer) pattern;
        match(kLabelFreezer.term(), otherKLabelFreezer.term());
    }

    @Override
    public void match(KLabelInjection kLabelInjection, Term pattern) {
        assert !(pattern instanceof Variable);

        if(!(pattern instanceof KLabelInjection)) {
            fail(kLabelInjection, pattern);
        }
        KLabelInjection otherKLabelInjection = (KLabelInjection) pattern;

        Kind injectionKind = kLabelInjection.term().kind();
        Kind otherInjectionKind = otherKLabelInjection.term().kind();
        if (injectionKind != otherInjectionKind
                && !(injectionKind.isComputational() && otherInjectionKind.isComputational())
                && !(injectionKind.isStructural() && otherInjectionKind.isStructural())) {
            fail(kLabelInjection, otherKLabelInjection);
        }

        match(kLabelInjection.term(), otherKLabelInjection.term());
    }

    @Override
    public void match(Hole hole, Term pattern) {
        assert !(pattern instanceof Variable);

        if (!hole.equals(pattern)) {
            fail(hole, pattern);
        }
    }

    @Override
    public void match(KItem kItem, Term pattern) {
        assert !(pattern instanceof Variable);

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
            if (kLabelConstant.isBinder()) {
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
                kList = new KList(ImmutableList.copyOf(terms));
            }
        }
        match(kList, patternKItem.kList());
    }

    @Override
    public void match(Token token, Term pattern) {
        assert !(pattern instanceof Variable);

        if (!token.equals(pattern)) {
            fail(token, pattern);
        }
    }

    @Override
    public void match(KList kList, Term pattern) {
        assert !(pattern instanceof Variable);

        if(!(pattern instanceof KList)) {
            fail(kList, pattern);
        }

        KList otherKList = (KList) pattern;
        matchKCollection(kList, otherKList);
    }

    @Override
    public void match(KSequence kSequence, Term pattern) {
        assert !(pattern instanceof Variable);

        if (!(pattern instanceof KSequence)) {
            this.fail(kSequence, pattern);
        }

        KSequence otherKSequence = (KSequence) pattern;
        matchKCollection(kSequence, otherKSequence);
    }

    private void matchKCollection(KCollection kCollection, KCollection pattern) {
        assert kCollection.getClass().equals(pattern.getClass());
        
        assert !kCollection.hasFrame() : "the subject term should be ground";

        int length = pattern.size();
        if (kCollection.size() >= length) {
            if (pattern.hasFrame()) {
                addSubstitution(pattern.frame(), kCollection.fragment(length));
            } else if (kCollection.size() > length) {
                fail(kCollection, pattern);
            }
            
            for (int index = 0; index < length; ++index) {
                match(kCollection.get(index), pattern.get(index));
            }
        } else {
            fail(kCollection, pattern);
        }
    }
    
    @Override
    public void match(MetaVariable metaVariable, Term pattern) {
        assert !(pattern instanceof Variable);

        if (!metaVariable.equals(pattern)) {
            fail(metaVariable, pattern);
        }
    }

    @Override
    public void match(Variable variable, Term pattern) {
        assert false : "the subject term should be ground; but found variable " + variable;
    }
    
    @Override
    public String getName() {
        return this.getClass().toString();
    }

}
