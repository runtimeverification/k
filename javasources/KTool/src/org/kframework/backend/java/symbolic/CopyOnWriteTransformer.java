package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimap;


/**
 * @author AndreiS
 */
public class CopyOnWriteTransformer implements Transformer {

    protected final Definition definition;
	
	public CopyOnWriteTransformer( Definition definition) {
		this.definition = definition;
	}

    public CopyOnWriteTransformer() {
        this.definition = null;
    }
	
    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        // TODO(AndreiS): implement
        return builtinSet;
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
        Multimap<String, Cell> cells = HashMultimap.create();
        for (Map.Entry<String, Cell> entry : cellCollection.cellMap().entries()) {
            Cell cell = (Cell) entry.getValue().accept(this);
            cells.put(entry.getKey(), cell);
            change = change || cell != entry.getValue();
        }
        if (!change) {
            cells = cellCollection.cellMap();
        }

        if (cellCollection.hasFrame()) {
            Variable frame;
            Term transformedFrame = (Term) cellCollection.frame().accept(this);
            if (transformedFrame instanceof CellCollection) {
                cells.putAll(((CellCollection) transformedFrame).cellMap());
                frame = ((CellCollection) transformedFrame).hasFrame() ?
                        ((CellCollection) transformedFrame).frame() : null;
            } else {
                frame = (Variable) transformedFrame;
            }

            if (cells != cellCollection.cellMap() || frame != cellCollection.frame()) {
                cellCollection = new CellCollection(cells, frame, cellCollection.isStar());
            }
        } else {
            if (cells != cellCollection.cellMap()) {
                cellCollection = new CellCollection(cells, cellCollection.isStar());
            }
        }

        return cellCollection;
    }

    @Override
    public ASTNode transform(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KLabelConstant kLabelConstant) {
        return kLabelConstant;
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        Term term = (Term) kLabelFreezer.term().accept(this);
        if (term != kLabelFreezer.term()) {
            kLabelFreezer = new KLabelFreezer(term);
        }
        return kLabelFreezer;
    }

    @Override
    public ASTNode transform(Hole hole) {
        return hole;
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        Term term = (Term) kLabelInjection.term().accept(this);
        if (term != kLabelInjection.term()) {
            kLabelInjection = new KLabelInjection(term);
        }
        return kLabelInjection;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        KLabel kLabel = (KLabel) kItem.kLabel().accept(this);
        KList kList = (KList) kItem.kList().accept(this);
        if (kLabel != kItem.kLabel() || kList != kItem.kList()) {
            kItem = new KItem(kLabel, kList, definition.context());
        }
        return kItem;
    }

    @Override
    public ASTNode transform(Token token) {
        return token;
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return transform((Token) boolToken);
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return transform((Token) intToken);
    }

    @Override
    public ASTNode transform(KCollection kCollection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(KLabel kLabel) {
        return kLabel;
    }

    @Override
    public ASTNode transform(KList kList) {
        List<Term> items = transformList(kList.getItems());

        if (kList.hasFrame()) {
            Variable frame = (Variable) kList.frame().accept(this);
            if (items != kList.getItems() || frame != kList.frame()) {
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
            Variable frame;
            Term transformedFrame = (Term) kSequence.frame().accept(this);
            if (transformedFrame instanceof KSequence) {
                items = new ArrayList<Term>(items);
                items.addAll(((KSequence) transformedFrame).getItems());
                frame = ((KSequence) transformedFrame).hasFrame() ?
                        ((KSequence) transformedFrame).frame() : null;
            } else {
                frame = (Variable) transformedFrame;
            }
            if (items != kSequence.getItems() || frame != kSequence.frame()) {
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
    public ASTNode transform(BuiltinMap builtinMap) {
        BuiltinMap transformedMap = null;
        if (builtinMap.hasFrame()) {
            Variable frame = (Variable) builtinMap.frame().accept(this);
            if (frame != builtinMap.frame()) {
                transformedMap = new BuiltinMap(frame);
            }
        }

        for(Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);

            if (transformedMap == null && (key != entry.getKey() || value != entry.getValue())) {
                if (builtinMap.hasFrame()) {
                    transformedMap = new BuiltinMap(builtinMap.frame());
                } else {
                    transformedMap = new BuiltinMap();
                }
                for(Map.Entry<Term, Term> copyEntry : builtinMap.getEntries().entrySet()) {
                    if (copyEntry.equals(entry)) {
                        break;
                    }
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
            return builtinMap;
        }
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        Term map = (Term) mapLookup.map().accept(this);
        Term key = (Term) mapLookup.key().accept(this);
        if (map != mapLookup.map() || key != mapLookup.key()) {
            mapLookup = new MapLookup(map, key);
        }
        return mapLookup;

    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        Term map = (Term) mapUpdate.map().accept(this);

        java.util.Set<Term> removeSet = null;
        for(Term key : mapUpdate.removeSet()) {
            Term transformedKey = (Term) key.accept(this);

            if (removeSet == null && transformedKey != key) {
                removeSet = new HashSet<Term>(mapUpdate.removeSet().size());
                for(Term copyKey : mapUpdate.removeSet()) {
                    if (copyKey == key) {
                        break;
                    }
                    removeSet.add(copyKey);
                }
            }

            if (removeSet != null) {
                removeSet.add(transformedKey);
            }
        }
        if (removeSet == null) {
            removeSet = mapUpdate.removeSet();
        }

        Map<Term, Term> updateMap = null;
        for(java.util.Map.Entry<Term, Term> entry : mapUpdate.updateMap().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);

            if (updateMap == null && (key != entry.getKey() || value != entry.getValue())) {
                updateMap = new HashMap<Term, Term>(mapUpdate.updateMap().size());
                for(Map.Entry<Term, Term> copyEntry : mapUpdate.updateMap().entrySet()) {
                    if (copyEntry.equals(entry)) {
                        break;
                    }
                    updateMap.put(copyEntry.getKey(), copyEntry.getValue());
                }
            }

            if (updateMap != null) {
                updateMap.put(key, value);
            }
        }
        if (updateMap == null) {
            updateMap = mapUpdate.updateMap();
        }

        if (map != mapUpdate.map() || removeSet != mapUpdate.removeSet()
                || mapUpdate.updateMap() != updateMap) {
            mapUpdate = new MapUpdate(map, removeSet, updateMap);
        }

        return mapUpdate;
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        Term set = (Term) setUpdate.base().accept(this);

        java.util.Set<Term> removeSet = null;
        for(Term key : setUpdate.removeSet()) {
            Term transformedKey = (Term) key.accept(this);

            if (removeSet == null && transformedKey != key) {
                removeSet = new HashSet<Term>(setUpdate.removeSet().size());
                for(Term copyKey : setUpdate.removeSet()) {
                    if (copyKey == key) {
                        break;
                    }
                    removeSet.add(copyKey);
                }
            }

            if (removeSet != null) {
                removeSet.add(transformedKey);
            }
        }
        if (removeSet == null) {
            removeSet = setUpdate.removeSet();
        }

        java.util.Set<Term> updateSet = null;
        for(Term key : setUpdate.updateSet()) {
            Term transformedKey = (Term) key.accept(this);

            if (updateSet == null && transformedKey != key) {
                updateSet = new HashSet<Term>(setUpdate.updateSet().size());
                for(Term copyKey : setUpdate.updateSet()) {
                    if (copyKey.equals(key)) {
                        break;
                    }
                    updateSet.add(copyKey);
                }
            }

            if (updateSet != null) {
                updateSet.add(transformedKey);
            }
        }
        if (updateSet == null) {
            updateSet = setUpdate.updateSet();
        }

        if (set != setUpdate.base() || removeSet != setUpdate.removeSet()
                || setUpdate.updateSet() != updateSet) {
            setUpdate = new SetUpdate(set, removeSet, updateSet);
        }

        return setUpdate;
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        Term base = (Term) setLookup.base().accept(this);
        Term key = (Term) setLookup.key().accept(this);
        if (base != setLookup.base() || key != setLookup.key()) {
            setLookup = new SetLookup(base, key);
        }
        return setLookup;
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public ASTNode transform(SymbolicConstraint symbolicConstraint) {
        SymbolicConstraint transformedSymbolicConstraint = new SymbolicConstraint(definition);

        for (Map.Entry<Variable, Term> entry : symbolicConstraint.substitution().entrySet()) {
            transformedSymbolicConstraint.add(
                    (Term) entry.getKey().accept(this),
                    (Term) entry.getValue().accept(this));
        }

        for (SymbolicConstraint.Equality equality : symbolicConstraint.equalities()) {
            transformedSymbolicConstraint.add(
                    (Term) equality.leftHandSide().accept(this),
                    (Term) equality.rightHandSide().accept(this));
        }

        return transformedSymbolicConstraint;
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
