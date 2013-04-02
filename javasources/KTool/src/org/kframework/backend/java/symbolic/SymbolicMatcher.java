package org.kframework.backend.java.symbolic;

import org.kframework.kil.matchers.MatcherException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;


/**
 * assumtions:
 *     Collections with one element rather than the element directly
 */
public class SymbolicMatcher extends AbstractMatcher {

    //private final Map<Variable, ListIterator> kCollectionSubstitution = new HashMap<>();
    private final java.util.Map<Variable, Term> substitution = new HashMap<Variable, Term>();
    private final java.util.Set<SymbolicEquality> constraints = new HashSet<SymbolicEquality>();
    private final java.util.Map<Variable, Term> freshSubstitution = new HashMap<Variable, Term>();

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    public Set<SymbolicEquality> getConstraints() {
        return constraints;
    }

    public boolean isMatching(Term term, Term pattern) {
        substitution.clear();
        constraints.clear();
        freshSubstitution.clear();

        try {
            match(term, pattern);
            return true;
        } catch (MatcherException e) {
            substitution.clear();
            constraints.clear();
            freshSubstitution.clear();
            return false;
        }
    }

    public void match(Term term, Term pattern) {
        /*
        System.err.println(">>>");
        System.err.println(term);
        System.err.println("<<<");
        System.err.println(pattern);
        System.err.println("===");
        */

        if (term.isSymbolic() || pattern.isSymbolic()) {
            constraints.add(new SymbolicEquality(term, pattern));
        } else {
            // match properly
            term.accept(this, pattern);
        }
    }


    /**
     * matches two builtin constants
     *
     * @param builtinConstant
     * @param pattern
     */
    @Override
    public void match(BuiltinConstant builtinConstant, Term pattern) {
        if (!(pattern instanceof BuiltinConstant)) {
            this.fail();
        }
        BuiltinConstant patternBuiltinConstant = (BuiltinConstant) pattern;

        if (!builtinConstant.equals(patternBuiltinConstant)) {
            fail();
        }
    }

    /**
     * matches two cells
     *
     * @param cell
     * @param pattern
     */
    @Override
    public void match(Cell cell, Term pattern) {
        if (!(pattern instanceof Cell)) {
            this.fail();
        }
        Cell patternCell = (Cell) pattern;

        if (!cell.getLabel().equals(patternCell.getLabel())
                || !cell.getContentKind().equals(patternCell.getContentKind())) {
            fail();
        }

        match(cell.getContent(), patternCell.getContent());
    }

    /**
     * matches two bags of cells
     *
     * @param cellCollection
     * @param pattern
     */
    @Override
    public void match(CellCollection cellCollection, Term pattern) {
        if (!(pattern instanceof CellCollection)) {
            this.fail();
        }
        CellCollection patternCellCollection = (CellCollection) pattern;

        java.util.Map<String, Cell> cellMap = new HashMap<String, Cell>();
        java.util.Map<String, Cell> patternCellMap = new HashMap<String, Cell>();

        for (String label : cellCollection.labelSet()) {
            if (patternCellCollection.containsKey(label)) {
                match(cellCollection.get(label), patternCellCollection.get(label));
            } else {
                cellMap.put(label, cellCollection.get(label));
            }
        }

        for (String label : patternCellCollection.labelSet()) {
            if (!cellCollection.containsKey(label)) {
                patternCellMap.put(label, patternCellCollection.get(label));
            }
        }

        if (cellCollection.hasFrame()) {
            if (patternCellCollection.hasFrame()) {
                Variable variable = AnonymousVariable.getFreshVariable("cellCollection");
                constraints.add(new SymbolicEquality(
                        cellCollection.getFrame(),
                        new CellCollection(patternCellMap, variable)));
                constraints.add(new SymbolicEquality(
                        new CellCollection(cellMap, variable),
                        patternCellCollection.getFrame()));
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }

                constraints.add(new SymbolicEquality(
                        cellCollection.getFrame(),
                        new CellCollection(patternCellMap)));
            }
        } else {
            if (!patternCellMap.isEmpty()) {
                fail();
            }

            if (patternCellCollection.hasFrame()) {
                constraints.add(new SymbolicEquality(
                        new CellCollection(cellMap),
                        patternCellCollection.getFrame()));
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }
            }
        }
    }

    /**
     * matches two KLabel constants
     *
     * @param constantKLabel
     * @param pattern
     */
    @Override
    public void match(ConstantKLabel constantKLabel, Term pattern) {
        if (!(pattern instanceof ConstantKLabel)) {
            this.fail();
        }
        ConstantKLabel patternConstantKLabel = (ConstantKLabel) pattern;

        if (!constantKLabel.equals(patternConstantKLabel)) {
            fail();
        }
    }

    @Override
    public void match(Hole hole, Term pattern) {
        if (!(pattern instanceof Hole)) {
            this.fail();
        }
        Hole patternHole = (Hole) pattern;

        if (!hole.equals(patternHole)) {
            fail();
        }
    }

    /**
     * matches two injection KLabel constants
     *
     * @param injectionKLabel
     * @param pattern
     */
    @Override
    public void match(InjectionKLabel injectionKLabel, Term pattern) {
        if(!(pattern instanceof InjectionKLabel)) {
            fail();
        }

        InjectionKLabel patternInjectionKLabel = (InjectionKLabel) pattern;
        match(injectionKLabel.getTerm(), patternInjectionKLabel.getTerm());
    }

    @Override
    public void match(K k, Term pattern) {
        if (!(pattern instanceof K)) {
            fail();
        }

        K patternK = (K) pattern;
        match(k.getKLabel(), patternK.getKLabel());
        match(k.getKList(), patternK.getKList());
    }

    @Override
    public void match(KList kList, Term pattern) {
        if(!(pattern instanceof KList)){
            fail();
        }

        KList patternKList = (KList) pattern;
        matchKCollection(kList, patternKList);
    }

    @Override
    public void match(KSequence kSequence, Term pattern) {
        if (!(pattern instanceof KSequence)) {
            this.fail();
        }

        KSequence patternKSequence = (KSequence) pattern;
        matchKCollection(kSequence, patternKSequence);
    }

    @SuppressWarnings("unchecked")
    public void matchKCollection(KCollection kCollection, KCollection patternKCollection) {
        int length = Math.min(kCollection.size(), kCollection.size());
        for(int index = 0; index < length; ++index) {
            this.match(kCollection.get(index), patternKCollection.get(index));
        }

        if (kCollection.size() < patternKCollection.size()) {
            if (!kCollection.hasFrame()) {
                fail();
            }

            KCollectionFragment fragment = new KCollectionFragment(patternKCollection, length);
            constraints.add(new SymbolicEquality(kCollection.getFrame(), fragment));
        } else if (patternKCollection.size() < kCollection.size()) {
            if (!patternKCollection.hasFrame()) {
                fail();
            }

            KCollectionFragment fragment = new KCollectionFragment(kCollection, length);
            constraints.add(new SymbolicEquality(fragment, patternKCollection.getFrame()));
        } else {
            if (kCollection.hasFrame() && patternKCollection.hasFrame()) {
                constraints.add(new SymbolicEquality(
                        kCollection.getFrame(),
                        patternKCollection.getFrame()));
            } else if (kCollection.hasFrame()) {
                KCollectionFragment fragment = new KCollectionFragment(patternKCollection, length);
                constraints.add(new SymbolicEquality(kCollection.getFrame(), fragment));
            } else if (patternKCollection.hasFrame()) {
                KCollectionFragment fragment = new KCollectionFragment(kCollection, length);
                constraints.add(new SymbolicEquality(fragment, patternKCollection.getFrame()));
            }
        }
    }

    @Override
    public void match(Map map, Term pattern) {
        if (!(pattern instanceof Map)) {
            this.fail();
        }

    }

    public void match(Variable variable, Term pattern) {
        throw new UnsupportedOperationException();
    }

}
