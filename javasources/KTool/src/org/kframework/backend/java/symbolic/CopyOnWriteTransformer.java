package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 6:54 PM
 * To change this template use File | Settings | File Templates.
 */
public class CopyOnWriteTransformer implements Transformer {

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public ASTNode transform(BuiltinConstant builtinConstant) {
        return builtinConstant;
    }

    @Override
    public ASTNode transform(Cell cell) {
        Term content = (Term) cell.getContent().accept(this);
        if (content != cell.getContent()) {
            cell = new Cell<Term>(cell.getLabel(), content);
        }
        return cell;
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        boolean change = false;
        java.util.Map<String, Cell> cells = new HashMap<String, Cell>(cellCollection.size());
        for (java.util.Map.Entry<String, Cell> entry: cellCollection.getCells().entrySet()) {
            Cell cell = (Cell) entry.getValue().accept(this);
            cells.put(entry.getKey(), cell);
            change = change || cell != entry.getValue();
        }
        if (!change) {
            cells = cellCollection.getCells();
        }

        if (cellCollection.hasFrame()) {
            Variable frame = (Variable) cellCollection.getFrame().accept(this);
            if (cells != cellCollection.getCells() || frame != cellCollection.getFrame()) {
                cellCollection = new CellCollection(cells, frame);
            }
        } else {
            if (cells != cellCollection.getCells()) {
                cellCollection = new CellCollection(cells);
            }
        }

        return cellCollection;
    }

    @Override
    public ASTNode transform(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return kLabelConstant;
    }

    @Override
    public ASTNode transform(Hole hole) {
        return hole;
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        Term term = (Term) kLabelInjection.getTerm().accept(this);
        if (term != kLabelInjection.getTerm()) {
            kLabelInjection = new KLabelInjection(term);
        }
        return kLabelInjection;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        KLabel kLabel = (KLabel) kItem.getKLabel().accept(this);
        KList kList = (KList) kItem.getKList().accept(this);
        if (kLabel != kItem.getKLabel() || kList != kItem.getKList()) {
            kItem = new KItem(kLabel, kList);
        }
        return kItem;
    }

    @Override
    public ASTNode transform(KCollection kCollection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KLabel kLabel) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KList kList) {
        List<Term> items = transformList(kList.getItems());

        if (kList.hasFrame()) {
            Variable frame = (Variable) kList.getFrame().accept(this);
            if (items != kList.getItems() || frame != kList.getFrame()) {
                kList = new KList(ImmutableList.<Term>copyOf(items), frame);
            }
        } else {
            if (items != kList.getItems()) {
                kList = new KList(ImmutableList.<Term>copyOf(items));
            }
        }

        return kList;
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        List<Term> items = transformList(kSequence.getItems());

        if (kSequence.hasFrame()) {
            Variable frame = (Variable) kSequence.getFrame().accept(this);
            if (items != kSequence.getItems() || frame != kSequence.getFrame()) {
                kSequence = new KSequence(ImmutableList.<Term>copyOf(items), frame);
            }
        } else {
            if (items != kSequence.getItems()) {
                kSequence = new KSequence(ImmutableList.<Term>copyOf(items));
            }
        }

        return kSequence;
    }

    @Override
    public ASTNode transform(Map map) {
        Map transformedMap = null;
        if (map.hasFrame()) {
            Variable frame = (Variable) map.getFrame().accept(this);
            if (frame != map.getFrame()) {
                transformedMap = new Map(frame);
            }
        }

        for(java.util.Map.Entry<Term, Term> entry : map.getEntries().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);

            if (transformedMap != null && (key != entry.getKey() || value != entry.getValue())) {
                if (map.hasFrame()) {
                    transformedMap = new Map(map.getFrame());
                } else {
                    transformedMap = new Map();
                }
                for(java.util.Map.Entry<Term, Term> copyEntry : map.getEntries().entrySet()) {
                    transformedMap.put(copyEntry.getKey(), copyEntry.getValue());
                }
            }

            if (transformedMap != null) {
                transformedMap.put(key, value);
            }
        }

        if (transformedMap != null) {
            return transformedMap;
        } else {
            return map;
        }
    }

    @Override
    public ASTNode transform(Rule rule) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(Term node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(Variable variable) {
        return variable;
    }

    protected List<Term> transformList(List<Term> list) {
        ArrayList<Term> transformedList = null;
        for (int index = 0; index < list.size(); ++index) {
            Term transformedTerm = (Term) list.get(index).accept(this);
            if (transformedList != null) {
                transformedList.add(transformedTerm);
            } else if (transformedTerm != list.get(index)) {
                transformedList = new ArrayList<Term>(list.size());
                for (int copyIndex = 0; copyIndex < index; ++copyIndex) {
                    transformedList.add(list.get(copyIndex));
                }
                transformedList.add(transformedTerm);
            }
        }

        if (transformedList != null) {
            return transformedList;
        } else {
            return list;
        }
    }

}
