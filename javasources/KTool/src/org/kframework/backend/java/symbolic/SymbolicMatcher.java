package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.AnonymousVariable;
import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.K;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.matchers.MatcherException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;


/**
 * assumtions:
 *     Collections with one element rather than the element directly
 */
public class SymbolicMatcher extends AbstractMatcher {

    //private final Map<Variable, ListIterator> kCollectionSubstitution = new HashMap<>();
    private SymbolicConstraint constraint = null;
    private final ArrayList<MapMatcher> mapMatchers = new ArrayList<MapMatcher>();

    private class MapMatcher {

        private Map map;
        private Map pattern;

        private MapMatcher(Map map, Map pattern) {
            this.map = new Map(new HashMap<Term, Term>(map.getEntries()));
            this.pattern =  new Map(new HashMap<Term, Term>(pattern.getEntries()));
        }

        private boolean incrementalMatch() {
            if (map == null && pattern == null) {
                return false;
            }

            boolean change = false;

            map = (Map) map.substitute(constraint.getSubstitution());
            pattern = (Map) pattern.substitute(constraint.getSubstitution());

            Iterator<java.util.Map.Entry<Term, Term>> iterator;
            iterator = map.getEntries().entrySet().iterator();
            while (iterator.hasNext()) {
                java.util.Map.Entry<Term, Term> entry = iterator.next();
                Term term = pattern.getEntries().get(entry.getKey());
                if (term != null) {
                    iterator.remove();
                    constraint.add(entry.getValue(), term);
                    change = true;
                }
            }

            iterator = pattern.getEntries().entrySet().iterator();
            while (iterator.hasNext()) {
                java.util.Map.Entry<Term, Term> entry = iterator.next();
                Term term = map.getEntries().get(entry.getKey());
                if (term != null) {
                    iterator.remove();
                    constraint.add(term, entry.getValue());
                    change = true;
                }
            }

            if (map.getEntries().isEmpty() && pattern.getEntries().isEmpty()) {
                if (map.hasFrame() && pattern.hasFrame()) {
                    constraint.add(map.getFrame(), pattern.getFrame());
                } else if (map.hasFrame()) {
                    constraint.add(map.getFrame(), Map.EMPTY);
                } else if (pattern.hasFrame()) {
                    constraint.add(Map.EMPTY, pattern.getFrame());
                }
                map = pattern = null;
            } else if (map.getEntries().isEmpty()) {
                if (map.hasFrame()) {
                    constraint.add(map.getFrame(), pattern);
                } else {
                    fail();
                }
                map = pattern = null;
            } else if (pattern.getEntries().isEmpty()) {
                if (pattern.hasFrame()) {
                    constraint.add(map, pattern.getFrame());
                } else {
                    fail();
                }
                map = pattern = null;
            }

            return change;
        }

    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    public SymbolicConstraint getConstraint() {
        return constraint;
    }

    public boolean isMatching(Term term, Term pattern) {
        constraint = new SymbolicConstraint();

        try {
            match(term, pattern);

            boolean change;
            do {
                change = false;

                for (MapMatcher mapMatcher : mapMatchers) {
                    change = change || mapMatcher.incrementalMatch();
                }

            } while (change);

            return true;
        } catch (MatcherException e) {
            constraint = null;
            return false;
        } finally {
            mapMatchers.clear();
            //freshSubstitution.clear();
        }
    }

    public void match(Term term, Term pattern) {
        System.err.println(">>>");
        System.err.println(term);
        System.err.println("<<<");
        System.err.println(pattern);
        System.err.println("===");

        if (term.isSymbolic() || pattern.isSymbolic()) {
            constraint.add(term, pattern);
            if (constraint.isFalse()) {
                fail();
            }
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
                constraint.add(
                        cellCollection.getFrame(),
                        new CellCollection(patternCellMap, variable));
                constraint.add(
                        new CellCollection(cellMap, variable),
                        patternCellCollection.getFrame());
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }

                constraint.add(cellCollection.getFrame(), new CellCollection(patternCellMap));
            }
        } else {
            if (!patternCellMap.isEmpty()) {
                fail();
            }

            if (patternCellCollection.hasFrame()) {
                constraint.add(new CellCollection(cellMap), patternCellCollection.getFrame());
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
     * @param kLabelConstant
     * @param pattern
     */
    @Override
    public void match(KLabelConstant kLabelConstant, Term pattern) {
        if (!(pattern instanceof KLabelConstant)) {
            this.fail();
        }
        KLabelConstant patternKLabelConstant = (KLabelConstant) pattern;

        if (!kLabelConstant.equals(patternKLabelConstant)) {
            fail();
        }
    }

    @Override
    public void match(KLabelFreezer kLabelFreezer, Term pattern) {
        if (!(pattern instanceof KLabelFreezer)) {
            this.fail();
        }
        KLabelFreezer patternKLabelFreezer = (KLabelFreezer) pattern;

        if (!kLabelFreezer.equals(patternKLabelFreezer)) {
            fail();
        }
    }

    /**
     * matches two injection KLabel constants
     *
     * @param kLabelInjection
     * @param pattern
     */
    @Override
    public void match(KLabelInjection kLabelInjection, Term pattern) {
        if(!(pattern instanceof KLabelInjection)) {
            fail();
        }

        KLabelInjection patternKLabelInjection = (KLabelInjection) pattern;
        match(kLabelInjection.getTerm(), patternKLabelInjection.getTerm());
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
            constraint.add(kCollection.getFrame(), fragment);
        } else if (patternKCollection.size() < kCollection.size()) {
            if (!patternKCollection.hasFrame()) {
                fail();
            }

            KCollectionFragment fragment = new KCollectionFragment(kCollection, length);
            constraint.add(fragment, patternKCollection.getFrame());
        } else {
            if (kCollection.hasFrame() && patternKCollection.hasFrame()) {
                constraint.add(kCollection.getFrame(), patternKCollection.getFrame());
            } else if (kCollection.hasFrame()) {
                KCollectionFragment fragment = new KCollectionFragment(patternKCollection, length);
                constraint.add(kCollection.getFrame(), fragment);
            } else if (patternKCollection.hasFrame()) {
                KCollectionFragment fragment = new KCollectionFragment(kCollection, length);
                constraint.add(fragment, patternKCollection.getFrame());
            }
        }
    }

    @Override
    public void match(Map map, Term pattern) {
        if (!(pattern instanceof Map)) {
            this.fail();
        }

        mapMatchers.add(new MapMatcher(map, (Map) pattern));
    }

    public void match(Variable variable, Term pattern) {
        throw new UnsupportedOperationException();
    }

}
