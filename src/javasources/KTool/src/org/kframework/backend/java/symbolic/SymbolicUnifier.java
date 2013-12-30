package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.matchers.MatcherException;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
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
    private final SymbolicConstraint fConstraint;
    
    /**
     * TODO(YilongL)
     */
    private boolean isStarNested;
    
    /**
     * A disjunction of {@code SymbolicConstraint}s created by this unifier.
     */
    public final java.util.Collection<java.util.Collection<SymbolicConstraint>> multiConstraints;
    private final TermContext context;

    public SymbolicUnifier(SymbolicConstraint constraint, TermContext context) {
        this.fConstraint = constraint;
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
            // TODO(YilongL): can we move this adhoc code to another place?
            /* special case for concrete collections  */
            if (term instanceof ConcreteCollectionVariable
                    && !matchConcreteSize((ConcreteCollectionVariable) term, otherTerm)) {
                fail();
            } else if (otherTerm instanceof ConcreteCollectionVariable
                    && !matchConcreteSize((ConcreteCollectionVariable) otherTerm, term)) {
                fail();
            }

            /* add symbolic constraint */
            fConstraint.add(term, otherTerm);
            if (fConstraint.isFalse()) {
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
        assert !(term instanceof Variable);
        
        if (!(term instanceof BuiltinList)) {
            this.fail();
        }
        
        throw new UnsupportedOperationException(
                "list matching is only supported when one of the lists is a variable.");
    }

    @Override
    public void unify(BuiltinMap builtinMap, Term term) {
        assert !(term instanceof Variable);
        
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
        assert !(term instanceof Variable);
        if (!(term instanceof BuiltinSet)) {
            this.fail();
        }

        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    /**
     * Two cells can be unified if and only if they have the same cell label and
     * their contents can be unified.
     */
    @Override
    public void unify(Cell cell, Term term) {
        assert !(term instanceof Variable);
        
        if (!(term instanceof Cell)) {
            this.fail();
        }

        Cell<?> otherCell = (Cell<?>) term;
        if (!cell.getLabel().equals(otherCell.getLabel())) {
            /*
             * AndreiS: commented out the check below as matching might fail due
             * to KItem < K < KList subsorting:
             * !cell.contentKind().equals(otherCell.contentKind())
             */            
            fail();
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
            fail();
        }
        CellCollection otherCellCollection = (CellCollection) term;

        /*
         * YilongL: the configuration structure of the subject term should be
         * concrete.
         */
        assert !cellCollection.hasFrame();

        Set<String> unifiableCellLabels = new HashSet<String>(cellCollection.labelSet());
        unifiableCellLabels.retainAll(otherCellCollection.labelSet());

        if (!cellCollection.hasStar()) {
            if (!otherCellCollection.hasStar()) {
                /* Case 1: TODO(YilongL) */
                for (String label : unifiableCellLabels) {
                    assert cellCollection.get(label).size() == 1
                            && otherCellCollection.get(label).size() == 1;
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

                // since cellCollection has no frame, otherCellMap must be empty
                if (!otherCellMap.isEmpty()) {
                    fail();
                }
                
                if (otherCellCollection.hasFrame()) {
                    fConstraint.add(new CellCollection(cellMap, false), otherCellCollection.frame());
                } else if (!cellMap.isEmpty()) {
                    // otherCellCollection has no frame and cellMap is not empty, fail
                    fail();
                }
            } else {
                /*
                 * Case 2: since cellCollection has no frame, the
                 * starred-cell(s) in otherCellCollection can never match
                 */
                fail();
            }
        } else {
            assert !isStarNested : "nested cells with multiplicity='*' not supported";
            // TODO(AndreiS): fix this assertions

            if (!otherCellCollection.hasStar()) {
                /* Case 3: otherCellCollection must be a single frame */
                if (! (otherCellCollection.cells().isEmpty() && otherCellCollection.hasFrame())) {
                    fail();
                }
                
                fConstraint.add(new CellCollection(cellCollection.cellMap(),
                        true), otherCellCollection.frame());
            } else {
                /*
                 * Case 4: the two cell collections must have one common type of
                 * starred-cells
                 */
                
                if (unifiableCellLabels.size() != 1) {
                    fail();
                }
                
                if (cellCollection.size() < otherCellCollection.size()
                        || cellCollection.size() > otherCellCollection.size()
                        && !otherCellCollection.hasFrame()) {
                    fail();
                }

                String label = unifiableCellLabels.iterator().next();
                Cell<?>[] cells = cellCollection.get(label).toArray(new Cell[1]);
                Cell<?>[] otherCells = otherCellCollection.get(label).toArray(new Cell[1]);
                Variable otherFrame = otherCellCollection.hasFrame() ? otherCellCollection.frame() : null;

                isStarNested = true;

                java.util.Collection<SymbolicConstraint> constraints = new ArrayList<SymbolicConstraint>();
                SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
                do {
                    SymbolicConstraint constraint = new SymbolicConstraint(context);

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

                isStarNested = false;

                if (constraints.isEmpty()) {
                    fail();
                }

                if (constraints.size() == 1) {
                    fConstraint.addAll(constraints.iterator().next());
                } else {
                    multiConstraints.add(constraints);
                }
            }
        }
        

//        if (cellCollection.hasStar() != otherCellCollection.hasStar() && !otherCellCollection.cells().isEmpty()) {
//            fail();
//        }
//
////        Set<String> unifiableCellLabels = new HashSet<String>(cellCollection.labelSet());
////        unifiableCellLabels.retainAll(otherCellCollection.labelSet());
//
//        if (!cellCollection.hasStar()) {
//            for (String label : unifiableCellLabels) {
//                unify(cellCollection.get(label).iterator().next(),
//                      otherCellCollection.get(label).iterator().next());
//            }
//
//            Multimap<String, Cell> cellMap = ArrayListMultimap.create();
//            for (String label : cellCollection.labelSet()) {
//                if (!unifiableCellLabels.contains(label)) {
//                    cellMap.putAll(label, cellCollection.get(label));
//                }
//            }
//
//            Multimap<String, Cell> otherCellMap = ArrayListMultimap.create();
//            for (String label : otherCellCollection.labelSet()) {
//                if (!unifiableCellLabels.contains(label)) {
//                    otherCellMap.putAll(label, otherCellCollection.get(label));
//                }
//            }
//
//            addCellCollectionConstraint(
//                    cellMap,
//                    cellCollection.hasFrame() ? cellCollection.frame() : null,
//                    otherCellMap,
//                    otherCellCollection.hasFrame() ? otherCellCollection.frame() : null,
//                    cellCollection.hasStar());
//        } else {
//            assert !isStarNested : "nested cells with multiplicity='*' not supported";
//            // TODO(AndreiS): fix this assertions
//            //assert !cellCollection.hasFrame();
//            //assert cellCollection.size() >= otherCellCollection.size();
//            if (!(!cellCollection.hasFrame() && cellCollection.size() >= otherCellCollection.size())) {
//                fail();
//            }
//
//            Cell[] otherCells;
//            Cell[] cells;
//            if (!otherCellCollection.cells().isEmpty()) {
//                String label = unifiableCellLabels.iterator().next();
//                cells = cellCollection.get(label).toArray(new Cell[0]);
//                otherCells = otherCellCollection.get(label).toArray(new Cell[0]);
//            } else {
//                String label = cellCollection.labelSet().iterator().next();
//                cells = cellCollection.get(label).toArray(new Cell[0]);
//                otherCells = new Cell[0];
//            }
//            Variable otherFrame = otherCellCollection.hasFrame() ? otherCellCollection.frame() : null;
//
//            if (otherFrame == null && cells.length > otherCells.length) {
//                fail();
//            }
//
//            isStarNested = true;
//
//            java.util.Collection<SymbolicConstraint> constraints = new ArrayList<SymbolicConstraint>();
//            SelectionGenerator generator = new SelectionGenerator(otherCells.length, cells.length);
//            do {
//                SymbolicConstraint constraint = new SymbolicConstraint(context);
//
//                try {
//                    for (int i = 0; i < otherCells.length; ++i) {
//                        unify(cells[generator.selection.get(i)], otherCells[i]);
//                    }
//                } catch (MatcherException e) {
//                    continue;
//                }
//
//                Multimap<String, Cell> cellMap = ArrayListMultimap.create();
//                for (int i = 0; i < cells.length; ++i) {
//                    if (!generator.selected.contains(i)) {
//                        cellMap.put(cells[i].getLabel(), cells[i]);
//                    }
//                }
//
//                if (otherFrame != null) {
//                    constraint.add(new CellCollection(cellMap, true), otherFrame);
//                } else {
//                    if (!cellMap.isEmpty()) fail();
//                }
//                constraints.add(constraint);
//            } while (generator.generate());
//
//            isStarNested = false;
//
//            if (constraints.isEmpty()) {
//                fail();
//            }
//
//            if (constraints.size() == 1) {
//                fConstraint.addAll(constraints.iterator().next());
//            } else {
//                multiConstraints.add(constraints);
//            }
//        }
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
            boolean hasStar) {
        if (frame != null) {
            if (otherFrame != null) {
                if (cellMap.isEmpty() && otherCellMap.isEmpty()) {
                    fConstraint.add(frame, otherFrame);
                } else if (cellMap.isEmpty()) {
                    fConstraint.add(frame, new CellCollection(otherCellMap, otherFrame, hasStar));
                } else if (otherCellMap.isEmpty()) {
                    fConstraint.add(new CellCollection(cellMap, frame, hasStar), otherFrame);
                } else {
                    Variable variable = Variable.getFreshVariable(Kind.CELL_COLLECTION.toString());
                    fConstraint.add(frame, new CellCollection(otherCellMap, variable, hasStar));
                    fConstraint.add(new CellCollection(cellMap, variable, hasStar), otherFrame);
                }
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }

                fConstraint.add(frame, new CellCollection(otherCellMap, hasStar));
            }
        } else {
            if (otherFrame != null) {
                if (!otherCellMap.isEmpty()) {
                    fail();
                }

                fConstraint.add(new CellCollection(cellMap, hasStar), otherFrame);
            } else {
                if (!cellMap.isEmpty() || !otherCellMap.isEmpty()) {
                    fail();
                }
            }
        }
    }

    @Override
    public void unify(KLabelConstant kLabelConstant, Term term) {
        assert !(term instanceof Variable);
        
        if (!kLabelConstant.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(KLabelFreezer kLabelFreezer, Term term) {
        assert !(term instanceof Variable);

        if(!(term instanceof KLabelFreezer)) {
            fail();
        }

        KLabelFreezer otherKLabelFreezer = (KLabelFreezer) term;
        unify(kLabelFreezer.term(), otherKLabelFreezer.term());
    }

    @Override
    public void unify(KLabelInjection kLabelInjection, Term term) {
        assert !(term instanceof Variable);

        if(!(term instanceof KLabelInjection)) {
            fail();
        }

        KLabelInjection otherKLabelInjection = (KLabelInjection) term;
        unify(kLabelInjection.term(), otherKLabelInjection.term());
    }

    @Override
    public void unify(Hole hole, Term term) {
        assert !(term instanceof Variable);

        if (!hole.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(KItem kItem, Term term) {
        assert !(term instanceof Variable);

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
        assert !(term instanceof Variable);

        if (!token.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(UninterpretedToken uninterpretedToken, Term term) {
        assert !(term instanceof Variable);

        if (!uninterpretedToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(BoolToken boolToken, Term term) {
        assert !(term instanceof Variable);

        if (!boolToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(IntToken intToken, Term term) {
        assert !(term instanceof Variable);

        if (!intToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(Int32Token intToken, Term term) {
        assert !(term instanceof Variable);

        if (!intToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(StringToken stringToken, Term term) {
        assert !(term instanceof Variable);

        if (!stringToken.equals(term)) {
            fail();
        }
    }

    @Override
    public void unify(KList kList, Term term) {
        assert !(term instanceof Variable);

        if(!(term instanceof KList)){
            fail();
        }

        KList otherKList = (KList) term;
        matchKCollection(kList, otherKList);
    }

    @Override
    public void unify(KSequence kSequence, Term term) {
        assert !(term instanceof Variable);

        if (!(term instanceof KSequence)) {
            this.fail();
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
                fail();
            }
            fConstraint.add(kCollection.frame(), otherKCollection.fragment(length));
        } else if (otherKCollection.size() < kCollection.size()) {
            if (!otherKCollection.hasFrame()) {
                fail();
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
