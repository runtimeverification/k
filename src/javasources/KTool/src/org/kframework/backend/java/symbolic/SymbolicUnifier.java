// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinMgu;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.SetUpdate;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimap;


/**
 * A unifier modulo theories.
 *
 * @author AndreiS
 */
public class SymbolicUnifier extends AbstractUnifier {

    public static class Data {
        /**
         * A conjunction of disjunctions of {@code SymbolicConstraint}s created by this unifier.
         */
        public Collection<Collection<SymbolicConstraint.Data>> multiConstraints;

        //TODO: the fields should be final

        public Data(Collection<Collection<SymbolicConstraint.Data>> multiConstraints) {
            this.multiConstraints = multiConstraints;
        }

        public Data() {
            this(new ArrayList<java.util.Collection<SymbolicConstraint.Data>>());
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result
                    + ((multiConstraints == null) ? 0 : multiConstraints.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Data other = (Data) obj;
            if (multiConstraints == null) {
                if (other.multiConstraints != null)
                    return false;
            } else if (!multiConstraints.equals(other.multiConstraints))
                return false;
            return true;
        }
    }

    /**
     * TODO(YilongL)
     */
    private boolean isStarNested;

    public final Data data;

    private final TermContext termContext;

    /**
     * Represents the existing {@code SymbolicConstraint} before invoking this
     * unifier and then becomes the overall {@code SymbolicConstraint} after the
     * unification is done.
     */
    private SymbolicConstraint fConstraint;

    public SymbolicUnifier(SymbolicConstraint constraint, TermContext context) {
        this(constraint, new Data(), context);
    }

    public SymbolicUnifier(SymbolicConstraint constraint, Data data, TermContext context) {
        this.fConstraint = constraint;
        this.termContext = context;
        this.data = data;
    }

    public Collection<Collection<SymbolicConstraint>> multiConstraints() {
        ArrayList<Collection<SymbolicConstraint>> multiConstraints = new ArrayList<>();
        for(Collection<SymbolicConstraint.Data> mcd: data.multiConstraints) {
            ArrayList<SymbolicConstraint> mc = new ArrayList<>();
            for(SymbolicConstraint.Data scd: mcd)
                mc.add(new SymbolicConstraint(scd, termContext));
            multiConstraints.add(mc);
        }
        return multiConstraints;
    }

    /**
     * Unifies the two sides of the given equality.
     *
     * @param equality
     *            the given equality
     * @return true if the unification succeeds; otherwise, false
     */
    public boolean unify(SymbolicConstraint.Equality equality) {
        try {
            isStarNested = false;
            // YilongL: is it correct to simply clear the multiConstraints?
            data.multiConstraints.clear();
            unify(equality.leftHandSide(), equality.rightHandSide());
            // YilongL: I think getting here only means syntactic unification doesn't fail; is this a latent bug?
            return true;
        } catch (UnificationFailure e) {
            return false;
        }
    }

    /**
     * Performs generic operations for the unification of two terms.
     * Term-specific operations are then delegated to the specific {@code unify}
     * method by overloading. That is to say, in general, the safe way to unify
     * any two terms is to invoke this generic {@code unify} method; do not
     * invoke the specialized ones directly unless you know exactly what you are
     * doing.
     */
    @Override
    public void unify(Term term, Term otherTerm) {
        if (term instanceof Bottom || otherTerm instanceof Bottom) {
            fail(term, otherTerm);
        }
        if (term.kind().isComputational()) {
            assert otherTerm.kind().isComputational();

            term = KCollection.upKind(term, otherTerm.kind());
            otherTerm = KCollection.upKind(otherTerm, term.kind());
        }

        if (term.kind() == Kind.CELL || term.kind() == Kind.CELL_COLLECTION) {
            Context context = termContext.definition().context();
            term = CellCollection.upKind(term, otherTerm.kind(), context);
            otherTerm = CellCollection.upKind(otherTerm, term.kind(), context);
        }

        // TODO(YilongL): may need to replace the following assertion to the
        // method fail() in the future because it crashes the Java rewrite
        // engine instead of just failing the unification process
        assert term.kind() == otherTerm.kind():
               "kind mismatch between " + term + " (" + term.kind() + ")"
               + " and " + otherTerm + " (" + otherTerm.kind() + ")";

        if (term.isSymbolic() || otherTerm.isSymbolic()) {
            // TODO(YilongL): can we move this adhoc code to another place?
            /* special case for concrete collections  */
            if (term instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) term).matchConcreteSize(otherTerm)) {
                fail(term, otherTerm);
            } else if (otherTerm instanceof ConcreteCollectionVariable
                    && !((ConcreteCollectionVariable) otherTerm).matchConcreteSize(term)) {
                fail(term, otherTerm);
            }

            /* add symbolic constraint */
            fConstraint.add(term, otherTerm);
            // YilongL: not the right time to check the truth value because it
            // may change the equalities
            // if (fConstraint.isFalse()) {
            //  fail();
            // }
        } else {
            /* unify */
            if (!term.equals(otherTerm)) {
                term.accept(this, otherTerm);
            }
        }
    }

    @Override
    public void unify(BuiltinList builtinList, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof BuiltinList)) {
            this.fail(builtinList, term);
        }

        throw new UnsupportedOperationException(
                "list matching is only supported when one of the lists is a variable.");
    }

    @Override
    public void unify(BuiltinMap builtinMap, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof BuiltinMap)) {
            this.fail(builtinMap, term);
        }
//        if (builtinMap.equals(BuiltinMap.EMPTY) && term.equals(BuiltinMap.EMPTY))
//            return;

        throw new UnsupportedOperationException(
                "map matching is only supported when one of the maps is a variable.");
    }

    @Override
    public void unify(MapUpdate mapUpdate, Term term) {
        // this method is only used during macro expansion of rewrite rules
        assert !(term instanceof Variable);

        if (!(term instanceof MapUpdate)) {
            this.fail(mapUpdate, term);
        }

        throw new UnsupportedOperationException(
                "Currently, mapUpdate can only be matched with a variable.");
    }

    @Override
    public void unify(BuiltinSet builtinSet, Term term) {
        assert !(term instanceof Variable);
        if (!(term instanceof BuiltinSet)) {
            this.fail(builtinSet, term);
        }

        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    @Override
    public void unify(SetUpdate setUpdate, Term term) {
        // this method is only used during macro expansion of rewrite rules
        assert !(term instanceof Variable);

        if (!(term instanceof SetUpdate)) {
            this.fail(setUpdate, term);
        }

        throw new UnsupportedOperationException(
                "Currently, setUpdate can only be matched with a variable.");
    }

    @Override
    public void unify(BuiltinMgu builtinMgu, Term term) {
        assert !(term instanceof Variable);
        if (!(term instanceof BuiltinMgu)) {
            this.fail(builtinMgu, term);
        }

        throw new UnsupportedOperationException(
                "Mgu matching is only supported when one of the Mgu's is a variable.");
    }

    /**
     * Two cells can be unified if and only if they have the same cell label and
     * their contents can be unified.
     */
    @Override
    public void unify(Cell cell, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof Cell)) {
            this.fail(cell, term);
        }

        Cell<?> otherCell = (Cell<?>) term;
        if (!cell.getLabel().equals(otherCell.getLabel())) {
            /*
             * AndreiS: commented out the check below as matching might fail due
             * to KItem < K < KList subsorting:
             * !cell.contentKind().equals(otherCell.contentKind())
             */
            fail(cell, otherCell);
        }

        unify(cell.getContent(), otherCell.getContent());
    }

    /**
     *
     */
    @Override
    public void unify(CellCollection cellCollection, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof CellCollection)) {
            fail(cellCollection, term);
        }
        CellCollection otherCellCollection = (CellCollection) term;

        if (cellCollection.hasStar() && !otherCellCollection.hasStar()) {
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

        Set<String> unifiableCellLabels = new HashSet<String>(cellCollection.labelSet());
        unifiableCellLabels.retainAll(otherCellCollection.labelSet());

        Context context = termContext.definition().context();

        /*
         * CASE 1: cellCollection has no explicitly specified starred-cell;
         * therefore, no need to worry about AC-unification at all!
         */
        if (!cellCollection.hasStar()) {
            for (String label : unifiableCellLabels) {
                assert cellCollection.get(label).size() == 1
                        && otherCellCollection.get(label).size() == 1;
                unify(cellCollection.get(label).iterator().next(),
                        otherCellCollection.get(label).iterator().next());
            }

            Multimap<String, Cell> cellMap = ArrayListMultimap.create();
            Multimap<String, Cell> otherCellMap = ArrayListMultimap.create();
            computeDisjointCellMaps(unifiableCellLabels, cellCollection,
                    cellMap, otherCellCollection, otherCellMap);

            if (!addCellCollectionConstraint(
                    cellMap,
                    cellCollection.hasFrame() ? cellCollection.frame() : null,
                    otherCellMap,
                    otherCellCollection.hasFrame() ? otherCellCollection.frame() : null)) {
                fail(cellCollection, otherCellCollection);
            }
        }
        /* Case 2: both cell collections have explicitly specified starred-cells */
        else {
            assert !isStarNested : "nested cells with multiplicity='*' not supported";
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
                    unify(cellCollection.get(cellLabel).iterator().next(),
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
            // temporarily store the current constraint at a safe place before
            // starting to search for multiple unifiers
            SymbolicConstraint mainConstraint = fConstraint;
            isStarNested = true;

            java.util.Collection<SymbolicConstraint> constraints = new ArrayList<SymbolicConstraint>();
            SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
            // start searching for all possible unifiers
            do {
                // clear the constraint before each attempt of unification
                fConstraint = new SymbolicConstraint(termContext);

                try {
                    for (int i = 0; i < otherCells.length; ++i) {
                        unify(cells[generator.selection.get(i)], otherCells[i]);
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
                    fConstraint.add(new CellCollection(cm, context), otherFrame);
                } else {
                    if (!cm.isEmpty()) fail(cellCollection, otherCellCollection);
                }
                constraints.add(fConstraint);
            } while (generator.generate());

            // restore the current constraint after searching
            fConstraint = mainConstraint;
            isStarNested = false;

            if (constraints.isEmpty()) {
                fail(cellCollection, otherCellCollection);
            }

            if (constraints.size() == 1) {
                fConstraint.addAll(constraints.iterator().next());
            } else {
                List<SymbolicConstraint.Data> constraintsData = new ArrayList<>();
                for(SymbolicConstraint c : constraints)
                    constraintsData.add(c.data);
                data.multiConstraints.add(constraintsData);
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
     * specialized cell collections. Two preconditions for the arguments: 1) The
     * two specified cell collections shall have no common cell label in their
     * explicit contents; 2) the first cell collection contains no starred-cell
     * in its explicit content.
     *
     * @return true if the constraint addition does not make the unification to fail
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

        Context context = termContext.definition().context();

        if (frame != null) {
            if (otherFrame != null) {
                if (cellMap.isEmpty() && otherCellMap.isEmpty()) {
                    fConstraint.add(frame, otherFrame);
                } else if (cellMap.isEmpty()) {
                    fConstraint.add(frame, new CellCollection(otherCellMap, otherFrame, context));
                } else if (otherCellMap.isEmpty()) {
                    fConstraint.add(new CellCollection(cellMap, frame, context), otherFrame);
                } else {
                    Variable variable = Variable.getFreshVariable(Kind.CELL_COLLECTION.asSort());
                    fConstraint.add(frame, new CellCollection(otherCellMap, variable, context));
                    fConstraint.add(new CellCollection(cellMap, variable, context), otherFrame);
                }
            } else {
                if (!cellMap.isEmpty()) {
                    return false;
                }

                fConstraint.add(frame, new CellCollection(otherCellMap, context));
            }
        } else {
            if (otherFrame != null) {
                if (!otherCellMap.isEmpty()) {
                    return false;
                }

                fConstraint.add(new CellCollection(cellMap, context), otherFrame);
            } else {
                if (!cellMap.isEmpty() || !otherCellMap.isEmpty()) {
                    return false;
                }
            }
        }

        return true;
    }

    @Override
    public void unify(KLabelConstant kLabelConstant, Term term) {
        assert !(term instanceof Variable);

        if (!kLabelConstant.equals(term)) {
            fail(kLabelConstant, term);
        }
    }

    @Override
    public void unify(KLabelFreezer kLabelFreezer, Term term) {
        assert !(term instanceof Variable);

        if(!(term instanceof KLabelFreezer)) {
            fail(kLabelFreezer, term);
        }

        KLabelFreezer otherKLabelFreezer = (KLabelFreezer) term;
        unify(kLabelFreezer.term(), otherKLabelFreezer.term());
    }

    @Override
    public void unify(KLabelInjection kLabelInjection, Term term) {
        assert !(term instanceof Variable);

        if(!(term instanceof KLabelInjection)) {
            fail(kLabelInjection, term);
        }
        KLabelInjection otherKLabelInjection = (KLabelInjection) term;

        Kind injectionKind = kLabelInjection.term().kind();
        Kind otherInjectionKind = otherKLabelInjection.term().kind();
        if (injectionKind != otherInjectionKind
                && !(injectionKind.isComputational() && otherInjectionKind.isComputational())
                && !(injectionKind.isStructural() && otherInjectionKind.isStructural())) {
            fail(kLabelInjection, otherKLabelInjection);
        }

        unify(kLabelInjection.term(), otherKLabelInjection.term());
    }

    @Override
    public void unify(Hole hole, Term term) {
        assert !(term instanceof Variable);

        if (!hole.equals(term)) {
            fail(hole, term);
        }
    }

    @Override
    public void unify(KItem kItem, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof KItem)) {
            fail(kItem, term);
        }

        KItem patternKItem = (KItem) term;
        Term kLabel = kItem.kLabel();
        Term kList = kItem.kList();
        unify(kLabel, patternKItem.kLabel());
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
                kList = new KList(terms);
            }
        }
        unify(kList, patternKItem.kList());
    }

    @Override
    public void unify(Token token, Term term) {
        assert !(term instanceof Variable);

        if (!token.equals(term)) {
            fail(token, term);
        }
    }

    @Override
    public void unify(UninterpretedToken uninterpretedToken, Term term) {
        assert !(term instanceof Variable);

        if (!uninterpretedToken.equals(term)) {
            fail(uninterpretedToken, term);
        }
    }

    @Override
    public void unify(BitVector bitVector, Term term) {
        assert !(term instanceof Variable);

        if (!bitVector.equals(term)) {
            fail(bitVector, term);
        }
    }

    @Override
    public void unify(BoolToken boolToken, Term term) {
        assert !(term instanceof Variable);

        if (!boolToken.equals(term)) {
            fail(boolToken, term);
        }
    }

    @Override
    public void unify(IntToken intToken, Term term) {
        assert !(term instanceof Variable);

        if (!intToken.equals(term)) {
            fail(intToken, term);
        }
    }

    @Override
    public void unify(StringToken stringToken, Term term) {
        assert !(term instanceof Variable);

        if (!stringToken.equals(term)) {
            fail(stringToken, term);
        }
    }

    @Override
    public void unify(KList kList, Term term) {
        assert !(term instanceof Variable);

        if(!(term instanceof KList)){
            fail(kList, term);
        }

        KList otherKList = (KList) term;
        matchKCollection(kList, otherKList);
    }

    @Override
    public void unify(KSequence kSequence, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof KSequence)) {
            this.fail(kSequence, term);
        }

        KSequence otherKSequence = (KSequence) term;
        matchKCollection(kSequence, otherKSequence);
    }

    private void matchKCollection(KCollection kCollection, KCollection otherKCollection) {
        assert kCollection.getClass().equals(otherKCollection.getClass());

        int length = Math.min(kCollection.size(), otherKCollection.size());
        for(int index = 0; index < length; ++index) {
            unify(kCollection.get(index), otherKCollection.get(index));
        }

        if (kCollection.size() < otherKCollection.size()) {
            if (!kCollection.hasFrame()) {
                fail(kCollection, otherKCollection);
            }
            fConstraint.add(kCollection.frame(), otherKCollection.fragment(length));
        } else if (otherKCollection.size() < kCollection.size()) {
            if (!otherKCollection.hasFrame()) {
                fail(kCollection, otherKCollection);
            }
            fConstraint.add(kCollection.fragment(length), otherKCollection.frame());
        } else {
            if (kCollection.hasFrame() && otherKCollection.hasFrame()) {
                fConstraint.add(kCollection.frame(), otherKCollection.frame());
            } else if (kCollection.hasFrame()) {
                fConstraint.add(kCollection.frame(), otherKCollection.fragment(length));
            } else if (otherKCollection.hasFrame()) {
                fConstraint.add(kCollection.fragment(length), otherKCollection.frame());
            }
        }
    }

    @Override
    public void unify(MetaVariable metaVariable, Term term) {
        // TODO(YilongL): not sure about the assertion below
        // assert !(term instanceof Variable);

        if (!metaVariable.equals(term)) {
            fail(metaVariable, term);
        }
    }

    @Override
    public void unify(Variable variable, Term term) {
        unify((Term) variable, term);
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

}
