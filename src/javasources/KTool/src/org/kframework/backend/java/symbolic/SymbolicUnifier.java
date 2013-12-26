package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.matchers.MatcherException;

import java.util.*;
import org.kframework.backend.java.kil.Collection;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;


/**
 * A unifier modulo theories.
 *
 * @author AndreiS
 */
public class SymbolicUnifier extends AbstractUnifier {

    /**
     * Represents the existing {@code SymbolicConstraint} before invoking this
     * unifier and then becomes the overall {@code SymbolicConstraint} after the
     * unification is done.
     */
    private SymbolicConstraint constraint;
    
    /**
     * TODO(YilongL)
     */
    private boolean isStarNested;
    
    /**
     * A disjunction of {@code SymbolicConstraint}s created by this unifier.
     */
    public java.util.Collection<java.util.Collection<SymbolicConstraint>> multiConstraints;
    private final TermContext context;

    public SymbolicUnifier(SymbolicConstraint constraint, TermContext context) {
        this.constraint = constraint;
        this.context = context;
        context.definition();
        multiConstraints = new ArrayList<java.util.Collection<SymbolicConstraint>>();
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
            multiConstraints.clear();
            unify(equality.leftHandSide(), equality.rightHandSide());
            return true;
        } catch (MatcherException e) {
            return false;
        }
    }

    @Override
    public void unify(Term term, Term otherTerm) {
        if (term instanceof Bottom || otherTerm instanceof Bottom) {
            fail();
        }
        if (term.kind() == Kind.KITEM || term.kind() == Kind.K || term.kind() == Kind.KLIST) {
            term = KCollection.upKind(term, otherTerm.kind());
            otherTerm = KCollection.upKind(otherTerm, term.kind());
        }

        assert term.kind() == otherTerm.kind():
               "kind mismatch between " + term + " (" + term.kind() + ")"
               + " and " + otherTerm + " (" + otherTerm.kind() + ")";

        if (term.isSymbolic() || otherTerm.isSymbolic()) {
            /* special case for concrete collections  */
            if (term instanceof ConcreteCollectionVariable
                    && !matchConcreteSize((ConcreteCollectionVariable) term, otherTerm)) {
                fail();
            } else if (otherTerm instanceof ConcreteCollectionVariable
                    && !matchConcreteSize((ConcreteCollectionVariable) otherTerm, term)) {
                fail();
            }

            /* add symbolic constraint */
            constraint.add(term, otherTerm);
            if (constraint.isFalse()) {
                fail();
            }
        } else {
            /* unify */
            term.accept(this, otherTerm);
        }
    }

    private boolean matchConcreteSize(ConcreteCollectionVariable variable, Term term) {
        if (term instanceof ConcreteCollectionVariable) {
            ConcreteCollectionVariable otherVariable = (ConcreteCollectionVariable) term;
            return variable.concreteCollectionSize() == otherVariable.concreteCollectionSize();
        }

        if (!(term instanceof Collection)) {
            return false;
        }
        Collection collection = (Collection) term;

        if (collection.hasFrame()) {
            return false;
        }

        if (collection instanceof BuiltinList) {
            BuiltinList list = (BuiltinList) collection;
            return variable.concreteCollectionSize()
                   == list.elementsLeft().size() + list.elementsRight().size();
        } else if (collection instanceof BuiltinMap) {
            BuiltinMap map = (BuiltinMap) collection;
            return variable.concreteCollectionSize() == map.getEntries().size();
        } else if (collection instanceof BuiltinSet) {
            BuiltinSet set = (BuiltinSet) collection;
            return variable.concreteCollectionSize() == set.elements().size();
        } else {
            assert false: "unexpected collection class";
            return false;
        }
    }

    @Override
    public void unify(BuiltinList builtinList, Term term) {
        if (!(term instanceof BuiltinList)) {
            this.fail();
        }

        throw new UnsupportedOperationException(
                "list matching is only supported when one of the lists is a variable.");
    }

    @Override
    public void unify(BuiltinMap builtinMap, Term term) {
        if (!(term instanceof BuiltinMap)) {
            this.fail();
        }
//        if (builtinMap.equals(BuiltinMap.EMPTY) && term.equals(BuiltinMap.EMPTY))
//            return;

        throw new UnsupportedOperationException(
                "map matching is only supported when one of the maps is a variable.");
    }

    @Override
    public void unify(BuiltinSet builtinSet, Term term) {
        if (!(term instanceof BuiltinSet)) {
            this.fail();
        }

        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    @Override
    public void unify(Cell cell, Term term) {
        if (!(term instanceof Cell)) {
            this.fail();
        }

        Cell otherCell = (Cell) term;
        if (!cell.getLabel().equals(otherCell.getLabel())) {
                // AndreiS: commented out the check below as matching might fail due to KItem < K
                // < KList subsorting
                //|| !cell.contentKind().equals(otherCell.contentKind())) {
            fail();
        }

        unify(cell.getContent(), otherCell.getContent());
    }

    @Override
    public void unify(CellCollection cellCollection, Term term) {
        if (!(term instanceof CellCollection)) {
            fail();
        }
        CellCollection otherCellCollection = (CellCollection) term;

        if (cellCollection.isStar() != otherCellCollection.isStar() && !otherCellCollection.cells().isEmpty()) {
            fail();
        }

        Set<String> unifiableCellLabels = new HashSet<String>(cellCollection.labelSet());
        unifiableCellLabels.retainAll(otherCellCollection.labelSet());

        if (!cellCollection.isStar()) {
            for (String label : unifiableCellLabels) {
                unify(cellCollection.get(label).iterator().next(),
                      otherCellCollection.get(label).iterator().next());
            }

            Multimap<String, Cell> cellMap = ArrayListMultimap.create();
            for (String label : cellCollection.labelSet()) {
                if (!unifiableCellLabels.contains(label)) {
                    cellMap.putAll(label, cellCollection.get(label));
                }
            }

            Multimap<String, Cell> otherCellMap = ArrayListMultimap.create();
            for (String label : otherCellCollection.labelSet()) {
                if (!unifiableCellLabels.contains(label)) {
                    otherCellMap.putAll(label, otherCellCollection.get(label));
                }
            }

            addCellCollectionConstraint(
                    cellMap,
                    cellCollection.hasFrame() ? cellCollection.frame() : null,
                    otherCellMap,
                    otherCellCollection.hasFrame() ? otherCellCollection.frame() : null,
                    cellCollection.isStar());
        } else {
            assert !isStarNested : "nested cells with multiplicity='*' not supported";
            // TODO(AndreiS): fix this assertions
            //assert !cellCollection.hasFrame();
            //assert cellCollection.size() >= otherCellCollection.size();
            if (!(!cellCollection.hasFrame() && cellCollection.size() >= otherCellCollection.size())) {
                fail();
            }

            Cell[] otherCells;
            Cell[] cells;
            if (!otherCellCollection.cells().isEmpty()) {
                String label = unifiableCellLabels.iterator().next();
                cells = cellCollection.get(label).toArray(new Cell[0]);
                otherCells = otherCellCollection.get(label).toArray(new Cell[0]);
            } else {
                String label = cellCollection.labelSet().iterator().next();
                cells = cellCollection.get(label).toArray(new Cell[0]);
                otherCells = new Cell[0];
            }
            Variable otherFrame = otherCellCollection.hasFrame() ? otherCellCollection.frame() : null;

            if (otherFrame == null && cells.length > otherCells.length) {
                fail();
            }

            SymbolicConstraint mainConstraint = constraint;
            isStarNested = true;

            java.util.Collection<SymbolicConstraint> constraints = new ArrayList<SymbolicConstraint>();
            SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
            do {
                constraint = new SymbolicConstraint(context);

                try {
                    for (int i = 0; i < otherCells.length; ++i) {
                        unify(cells[generator.selection.get(i)], otherCells[i]);
                    }
                } catch (MatcherException e) {
                    continue;
                }

                Multimap<String, Cell> cellMap = ArrayListMultimap.create();
                for (int i = 0; i < cells.length; ++i) {
                    if (!generator.selected.contains(i)) {
                        cellMap.put(cells[i].getLabel(), cells[i]);
                    }
                }

                if (otherFrame != null) {
                    constraint.add(new CellCollection(cellMap, true), otherFrame);
                } else {
                    if (!cellMap.isEmpty()) fail();
                }
                constraints.add(constraint);
            } while (generator.generate());

            constraint = mainConstraint;
            isStarNested = false;

            if (constraints.isEmpty()) {
                fail();
            }

            if (constraints.size() == 1) {
                constraint.addAll(constraints.iterator().next());
            } else {
                multiConstraints.add(constraints);
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

    private void addCellCollectionConstraint(
            Multimap<String, Cell> cellMap,
            Variable frame,
            Multimap<String, Cell> otherCellMap,
            Variable otherFrame,
            boolean isStar) {
        if (frame != null) {
            if (otherFrame != null) {
                if (cellMap.isEmpty() && otherCellMap.isEmpty()) {
                    constraint.add(frame, otherFrame);
                } else if (cellMap.isEmpty()) {
                    constraint.add(frame, new CellCollection(otherCellMap, otherFrame, isStar));
                } else if (otherCellMap.isEmpty()) {
                    constraint.add(new CellCollection(cellMap, frame, isStar), otherFrame);
                } else {
                    Variable variable = Variable.getFreshVariable(Kind.CELL_COLLECTION.toString());
                    constraint.add(frame, new CellCollection(otherCellMap, variable, isStar));
                    constraint.add(new CellCollection(cellMap, variable, isStar), otherFrame);
                }
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }

                constraint.add(frame, new CellCollection(otherCellMap, isStar));
            }
        } else {
            if (otherFrame != null) {
                if (!otherCellMap.isEmpty()) {
                    fail();
                }

                constraint.add(new CellCollection(cellMap, isStar), otherFrame);
            } else {
                if (!cellMap.isEmpty() || !otherCellMap.isEmpty()) {
                    fail();
                }
            }
        }
    }

    @Override
    public void unify(KLabelConstant kLabelConstant, Term term) {
        if (!kLabelConstant.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(KLabelFreezer kLabelFreezer, Term term) {
        if(!(term instanceof KLabelFreezer)) {
            fail();
        }

        KLabelFreezer otherKLabelFreezer = (KLabelFreezer) term;
        unify(kLabelFreezer.term(), otherKLabelFreezer.term());
    }

    @Override
    public void unify(KLabelInjection kLabelInjection, Term term) {
        if(!(term instanceof KLabelInjection)) {
            fail();
        }

        KLabelInjection otherKLabelInjection = (KLabelInjection) term;
        unify(kLabelInjection.term(), otherKLabelInjection.term());
    }

    @Override
    public void unify(Hole hole, Term term) {
        if (!hole.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(KItem kItem, Term term) {
        if (!(term instanceof KItem)) {
            fail();
        }

        KItem patternKItem = (KItem) term;
        KLabel kLabel = kItem.kLabel();
        KList kList = kItem.kList();
        unify(kLabel, patternKItem.kLabel());
        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isBinder()) {
                Multimap<Integer, Integer> binderMap = kLabelConstant.getBinderMap();
                List<Term> terms = new ArrayList<>(kList.getContents());
                for (Integer boundVarPosition : binderMap.keySet()) {
                    Term boundVars = terms.get(boundVarPosition);
                    Set<Variable> variables = boundVars.variableSet();
                    Map<Variable,Variable> freshSubstitution = Variable.getFreshSubstitution(variables);
                    Term freshBoundVars = boundVars.substituteWithBinders(freshSubstitution, context);
                    terms.set(boundVarPosition, freshBoundVars);
                    for (Integer bindingExpPosition : binderMap.get(boundVarPosition)) {
                        Term bindingExp = terms.get(bindingExpPosition);
                        Term freshbindingExp = bindingExp.substituteWithBinders(freshSubstitution, context);
                        terms.set(bindingExpPosition, freshbindingExp);
                    }
                }
                kList = new KList(ImmutableList.copyOf(terms));
            }
        }
        unify(kList, patternKItem.kList());
    }

    @Override
    public void unify(Token token, Term term) {
        if (!token.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(UninterpretedToken uninterpretedToken, Term term) {
        if (!uninterpretedToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(BoolToken boolToken, Term term) {
        if (!boolToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(IntToken intToken, Term term) {
        if (!intToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(Int32Token intToken, Term term) {
        if (!intToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(StringToken stringToken, Term term) {
        if (!stringToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(KList kList, Term term) {
        if(!(term instanceof KList)){
            fail();
        }

        KList otherKList = (KList) term;
        matchKCollection(kList, otherKList);
    }

    @Override
    public void unify(KSequence kSequence, Term term) {
        if (!(term instanceof KSequence)) {
            this.fail();
        }

        KSequence otherKSequence = (KSequence) term;
        matchKCollection(kSequence, otherKSequence);
    }

    private void matchKCollection(KCollection kCollection, KCollection otherKCollection) {
        int length = Math.min(kCollection.size(), otherKCollection.size());
        for(int index = 0; index < length; ++index) {
            unify(kCollection.get(index), otherKCollection.get(index));
        }

        if (kCollection.size() < otherKCollection.size()) {
            if (!kCollection.hasFrame()) {
                fail();
            }
            constraint.add(kCollection.frame(), otherKCollection.fragment(length));
        } else if (otherKCollection.size() < kCollection.size()) {
            if (!otherKCollection.hasFrame()) {
                fail();
            }
            constraint.add(kCollection.fragment(length), otherKCollection.frame());
        } else {
            if (kCollection.hasFrame() && otherKCollection.hasFrame()) {
                constraint.add(kCollection.frame(), otherKCollection.frame());
            } else if (kCollection.hasFrame()) {
                constraint.add(kCollection.frame(), otherKCollection.fragment(length));
            } else if (otherKCollection.hasFrame()) {
                constraint.add(kCollection.fragment(length), otherKCollection.frame());
            }
        }
    }

    @Override
    public void unify(MetaVariable metaVariable, Term term) {
        if (!metaVariable.equals(term)) {
            fail();
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
