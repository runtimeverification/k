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
import org.kframework.kil.matchers.MatcherException;

import java.util.HashMap;
import java.util.Map;

import com.google.common.collect.ImmutableList;


/**
 * A unifier modulo theories.
 *
 * @author AndreiS
 */
public class SymbolicUnifier extends AbstractUnifier {

    private final SymbolicConstraint constraint;

    public SymbolicUnifier(SymbolicConstraint constraint) {
        this.constraint = constraint;
    }

    public boolean unify(SymbolicConstraint.Equality equality) {
        try {
            unify(equality.leftHandSide(), equality.rightHandSide());
            return true;
        } catch (MatcherException e) {
            return false;
        }
    }

    @Override
    public void unify(Term term, Term otherTerm) {
        /* promote KItem to K, and then promote K to KList */
        if (term.kind() == Kind.KITEM
                && (otherTerm.kind() == Kind.K || otherTerm.kind() == Kind.KLIST)) {
            term = new KSequence(ImmutableList.of(term));
        } else if (otherTerm.kind() == Kind.KITEM
                && (term.kind() == Kind.K || term.kind() == Kind.KLIST)) {
            otherTerm = new KSequence(ImmutableList.of(otherTerm));
        }

        if (term instanceof KSequence && otherTerm instanceof KList) {
            term = new KList(ImmutableList.of(term));
        } else if (otherTerm instanceof KSequence && term instanceof KList) {
            otherTerm = new KList(ImmutableList.of(otherTerm));
        }

        assert term.kind() == otherTerm.kind():
               "kind mismatch between " + term + " (" + term.kind() + ")"
               + " and " + otherTerm + " (" + otherTerm.kind() + ")";

        if (term.isSymbolic() || otherTerm.isSymbolic()) {
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

    @Override
    public void unify(BuiltinMap builtinMap, Term term) {
        if (!(term instanceof BuiltinMap)) {
            this.fail();
        }

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
                //|| !cell.getContentKind().equals(otherCell.getContentKind())) {
            fail();
        }

        unify(cell.getContent(), otherCell.getContent());
    }

    @Override
    public void unify(CellCollection cellCollection, Term term) {
        if (!(term instanceof CellCollection)) {
            this.fail();
        }
        CellCollection otherCellCollection = (CellCollection) term;

        Map<String, Cell> cellMap = new HashMap<String, Cell>();
        Map<String, Cell> otherCellMap = new HashMap<String, Cell>();

        for (String label : cellCollection.labelSet()) {
            if (otherCellCollection.containsKey(label)) {
                unify(cellCollection.get(label), otherCellCollection.get(label));
            } else {
                cellMap.put(label, cellCollection.get(label));
            }
        }

        for (String label : otherCellCollection.labelSet()) {
            if (!cellCollection.containsKey(label)) {
                otherCellMap.put(label, otherCellCollection.get(label));
            }
        }

        if (cellCollection.hasFrame()) {
            if (otherCellCollection.hasFrame()) {
                if (cellMap.isEmpty() && otherCellMap.isEmpty()) {
                    constraint.add(cellCollection.getFrame(), otherCellCollection.getFrame());
                } else if (cellMap.isEmpty()) {
                    constraint.add(
                            cellCollection.getFrame(),
                            new CellCollection(otherCellMap, otherCellCollection.getFrame()));
                } else if (otherCellMap.isEmpty()) {
                    constraint.add(
                            new CellCollection(cellMap, cellCollection.getFrame()),
                            otherCellCollection.getFrame());
                } else {
                    Variable variable = AnonymousVariable.getFreshVariable(
                            Kind.CELL_COLLECTION.toString());
                    constraint.add(
                            cellCollection.getFrame(),
                            new CellCollection(otherCellMap, variable));
                    constraint.add(
                            new CellCollection(cellMap, variable),
                            otherCellCollection.getFrame());
                }
            } else {
                if (!cellMap.isEmpty()) {
                    fail();
                }

                constraint.add(cellCollection.getFrame(), new CellCollection(otherCellMap));
            }
        } else if (otherCellCollection.hasFrame()) {
            if (!otherCellMap.isEmpty()) {
                fail();
            }

            constraint.add(new CellCollection(cellMap), otherCellCollection.getFrame());
        } else if (!cellMap.isEmpty() || !otherCellMap.isEmpty()) {
            fail();
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
        unify(kItem.kLabel(), patternKItem.kLabel());
        unify(kItem.kList(), patternKItem.kList());
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
            constraint.add(kCollection.getFrame(), otherKCollection.fragment(length));
        } else if (otherKCollection.size() < kCollection.size()) {
            if (!otherKCollection.hasFrame()) {
                fail();
            }
            constraint.add(kCollection.fragment(length), otherKCollection.getFrame());
        } else {
            if (kCollection.hasFrame() && otherKCollection.hasFrame()) {
                constraint.add(kCollection.getFrame(), otherKCollection.getFrame());
            } else if (kCollection.hasFrame()) {
                constraint.add(kCollection.getFrame(), otherKCollection.fragment(length));
            } else if (otherKCollection.hasFrame()) {
                constraint.add(kCollection.fragment(length), otherKCollection.getFrame());
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
