package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.AnonymousVariable;
import org.kframework.backend.java.kil.BoolToken;
import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.IntToken;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;


/**
 *
 *
 * @author AndreiS
 */
public class SymbolicMatcher extends AbstractMatcher {

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

            map = (Map) map.substitute(constraint.substitution(), context);
            pattern = (Map) pattern.substitute(constraint.substitution(), context);

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

    private final Context context;
    //private final Map<Variable, ListIterator> kCollectionSubstitution = new HashMap<>();
    private SymbolicConstraint constraint = null;
    private final ArrayList<MapMatcher> mapMatchers = new ArrayList<MapMatcher>();

	public SymbolicMatcher(Context context) {
		this.context = context;
	}

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    public SymbolicConstraint constraint() {
        return constraint;
    }

    public boolean isMatching(Term term, Term pattern) {
        constraint = new SymbolicConstraint(context);

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
     */
    @Override
    public void match(KLabelInjection kLabelInjection, Term pattern) {
        if(!(pattern instanceof KLabelInjection)) {
            fail();
        }

        KLabelInjection patternKLabelInjection = (KLabelInjection) pattern;
        match(kLabelInjection.term(), patternKLabelInjection.term());
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
    public void match(KItem kItem, Term pattern) {
        if (!(pattern instanceof KItem)) {
            fail();
        }

        KItem patternKItem = (KItem) pattern;
        match(kItem.kLabel(), patternKItem.kLabel());
        match(kItem.kList(), patternKItem.kList());
    }

    @Override
    public void match(Token token, Term pattern) {
        if (!token.equals(pattern)) {
            fail();
        }
    }

    @Override
    public void match(BoolToken boolToken, Term pattern) {
        if (!boolToken.equals(pattern)) {
            fail();
        }
    }

    @Override
    public void match(IntToken intToken, Term pattern) {
        if (!intToken.equals(pattern)) {
            fail();
        }
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
        assert false: "dead code";

        if (!(pattern instanceof Map)) {
            this.fail();
        }

        mapMatchers.add(new MapMatcher(map, (Map) pattern));
    }

    public void match(Variable variable, Term pattern) {
        assert false: "dead code";
    }

}
