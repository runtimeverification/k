package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.AnonymousVariable;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;

import java.util.HashMap;
import java.util.Map;

import com.google.common.collect.ImmutableList;


/**
 * A unifier modulo theories.
 *
 * @author AndreiS
 */
public class SymbolicMatcher extends AbstractMatcher {

    private final Context context;
    private SymbolicConstraint constraint = null;

	public SymbolicMatcher(Context context) {
		this.context = context;
	}

    public SymbolicConstraint constraint() {
        return constraint;
    }

    public boolean isMatching(Term term, Term pattern) {
        try {
            constraint = new SymbolicConstraint(context);
            match(term, pattern);
            return true;
        } catch (MatcherException e) {
            constraint = null;
            return false;
        }
    }

    public void match(Term term, Term pattern) {
        /* promote KItem to K, and then promote K to KList */
        if (term.kind() == Kind.KITEM
                && (pattern.kind() == Kind.K || pattern.kind() == Kind.KLIST)) {
            term = new KSequence(ImmutableList.of(term));
        } else if (pattern.kind() == Kind.KITEM
                && (term.kind() == Kind.K || term.kind() == Kind.KLIST)) {
            pattern = new KSequence(ImmutableList.of(pattern));
        }

        if (term instanceof KSequence && pattern instanceof KList) {
            term = new KList(ImmutableList.of(term));
        } else if (pattern instanceof KSequence && term instanceof KList) {
            pattern = new KList(ImmutableList.of(pattern));
        }

        assert term.kind() == pattern.kind():
               "kind mismatch between " + term + " (" + term.kind() + ")"
               + " and " + pattern + " (" + pattern.kind() + ")";

        if (term.isSymbolic() || pattern.isSymbolic()) {
            /* add symbolic constraint */
            constraint.add(term, pattern);
            if (constraint.isFalse()) {
                fail();
            }
        } else {
            /* match */
            term.accept(this, pattern);
        }
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public void match(BuiltinMap builtinMap, Term pattern) {
        if (!(pattern instanceof BuiltinMap)) {
            this.fail();
        }

        throw new UnsupportedOperationException(
                "map matching is only supported when one of the maps is a variable.");
    }

    @Override
    public void match(BuiltinSet builtinSet, Term pattern) {
        if (!(pattern instanceof BuiltinSet)) {
            this.fail();
        }

        throw new UnsupportedOperationException(
                "set matching is only supported when one of the sets is a variable.");
    }

    @Override
    public void match(Cell cell, Term pattern) {
        if (!(pattern instanceof Cell)) {
            this.fail();
        }

        Cell patternCell = (Cell) pattern;
        if (!cell.getLabel().equals(patternCell.getLabel())) {
                // AndreiS: commented out the check below as matching might fail due to KItem < K
                // < KList subsorting
                //|| !cell.getContentKind().equals(patternCell.getContentKind())) {
            fail();
        }

        match(cell.getContent(), patternCell.getContent());
    }

    @Override
    public void match(CellCollection cellCollection, Term pattern) {
        if (!(pattern instanceof CellCollection)) {
            this.fail();
        }
        CellCollection patternCellCollection = (CellCollection) pattern;

        Map<String, Cell> cellMap = new HashMap<String, Cell>();
        Map<String, Cell> patternCellMap = new HashMap<String, Cell>();

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
                if (cellMap.isEmpty() && patternCellMap.isEmpty()) {
                    constraint.add(cellCollection.getFrame(), patternCellCollection.getFrame());
                } else if (cellMap.isEmpty()) {
                    constraint.add(
                            cellCollection.getFrame(),
                            new CellCollection(patternCellMap, patternCellCollection.getFrame()));
                } else if (patternCellMap.isEmpty()) {
                    constraint.add(
                            new CellCollection(cellMap, cellCollection.getFrame()),
                            patternCellCollection.getFrame());
                } else {
                    Variable variable = AnonymousVariable.getFreshVariable(
                            Kind.CELL_COLLECTION.toString());
                    constraint.add(
                            cellCollection.getFrame(),
                            new CellCollection(patternCellMap, variable));
                    constraint.add(
                            new CellCollection(cellMap, variable),
                            patternCellCollection.getFrame());
                }
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }

                constraint.add(cellCollection.getFrame(), new CellCollection(patternCellMap));
            }
        } else if (patternCellCollection.hasFrame()) {
            if (!patternCellMap.isEmpty()) {
                fail();
            }

            constraint.add(new CellCollection(cellMap), patternCellCollection.getFrame());
        } else if (!cellMap.isEmpty() || !patternCellMap.isEmpty()) {
            fail();
        }
    }

    @Override
    public void match(KLabelConstant kLabelConstant, Term pattern) {
        if (!kLabelConstant.equals(pattern)) {
            fail();
        }
    }

    @Override
    public void match(KLabelFreezer kLabelFreezer, Term pattern) {
        if(!(pattern instanceof KLabelFreezer)) {
            fail();
        }

        KLabelFreezer patternKLabelFreezer = (KLabelFreezer) pattern;
        match(kLabelFreezer.term(), patternKLabelFreezer.term());
    }

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
        if (!hole.equals(pattern)) {
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
    public void match(UninterpretedToken uninterpretedToken, Term pattern) {
        if (!uninterpretedToken.equals(pattern)) {
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

    private void matchKCollection(KCollection kCollection, KCollection patternKCollection) {
        int length = Math.min(kCollection.size(), patternKCollection.size());
        for(int index = 0; index < length; ++index) {
            this.match(kCollection.get(index), patternKCollection.get(index));
        }

        if (kCollection.size() < patternKCollection.size()) {
            if (!kCollection.hasFrame()) {
                fail();
            }

            constraint.add(kCollection.getFrame(), patternKCollection.fragment(length));
        } else if (patternKCollection.size() < kCollection.size()) {
            if (!patternKCollection.hasFrame()) {
                fail();
            }

            constraint.add(kCollection.fragment(length), patternKCollection.getFrame());
        } else {
            if (kCollection.hasFrame() && patternKCollection.hasFrame()) {
                constraint.add(kCollection.getFrame(), patternKCollection.getFrame());
            } else if (kCollection.hasFrame()) {
                constraint.add(kCollection.getFrame(), patternKCollection.fragment(length));
            } else if (patternKCollection.hasFrame()) {
                constraint.add(kCollection.fragment(length), patternKCollection.getFrame());
            }
        }
    }

    @Override
    public void match(MetaVariable metaVariable, Term pattern) {
        if (!metaVariable.equals(pattern)) {
            fail();
        }
    }

    @Override
    public void match(Variable variable, Term pattern) {
        match((Term) variable, pattern);
    }

}
