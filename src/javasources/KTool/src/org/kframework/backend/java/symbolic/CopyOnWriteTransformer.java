// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;


/**
 * Performs transformation in post-order using a copy-on-write(COW) strategy.
 * This class serves as an adapter class: it provides a default post-order
 * traversal behavior for each KIL node and avoids constructing a new copy of
 * the target node to return unless it is actually going to be mutated.
 * <p>
 * COW strategy allows safe sub-term sharing.
 * 
 * @author AndreiS
 */
public class CopyOnWriteTransformer implements Transformer {

    protected final TermContext context;
    protected final Definition definition;
    
    public CopyOnWriteTransformer(TermContext context) {
        this.context = context;
        this.definition = context.definition();
    }

    public CopyOnWriteTransformer() {
        this.context = null;
        this.definition = null;
    }
    
    @Override
    public String getName() {
        return this.getClass().toString();
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
        boolean changed = false;
        Multimap<String, Cell> cellMap = ArrayListMultimap.create();
        for (Map.Entry<String, Cell> entry : cellCollection.cellMap().entries()) {
            Cell<?> cell = (Cell<?>) entry.getValue().accept(this);
            cellMap.put(entry.getKey(), cell);
            changed = changed || cell != entry.getValue();
        }
        if (!changed) {
            cellMap = cellCollection.cellMap();
        }

        // starting from now, !changed <=> cellMap == cellCollection.cellMap() 
        List<Variable> transformedBaseTerms = Lists.newArrayList();
        for (Variable variable : cellCollection.baseTerms()) {
            Term transformedBaseTerm = (Term) variable.accept(this);
            if (transformedBaseTerm instanceof CellCollection) {
                if (!changed) {
                    cellMap = ArrayListMultimap.create(cellCollection.cellMap());
                    changed = true;
                }
                
                CellCollection transformedCellCollection = (CellCollection) transformedBaseTerm;
                cellMap.putAll(transformedCellCollection.cellMap());
                transformedBaseTerms.addAll(transformedCellCollection.baseTerms());                
            } else if (transformedBaseTerm instanceof Cell) {
                if (!changed) {
                    cellMap = ArrayListMultimap.create(cellCollection.cellMap());
                    changed = true;
                }

                Cell<?> transformedCell = (Cell<?>) transformedBaseTerm;
                cellMap.put(transformedCell.getLabel(), transformedCell);
            } else {
                changed = changed || variable != transformedBaseTerm;
                transformedBaseTerms.add((Variable) transformedBaseTerm);
            }
        }
        
        return changed ? new CellCollection(cellMap, transformedBaseTerms, definition.context()) : cellCollection;
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
    public ASTNode transform(KItemProjection kItemProjection) {
        Term term = (Term) kItemProjection.term().accept(this);
        if (term != kItemProjection.term()) {
            kItemProjection = new KItemProjection(kItemProjection.kind(), term);
        }
        return kItemProjection;
    }

    @Override
    public ASTNode transform(KItem kItem) {
        Term kLabel = (Term) kItem.kLabel().accept(this);
        Term kList = (Term) kItem.kList().accept(this);
        if (kLabel != kItem.kLabel() || kList != kItem.kList()) {
            kItem = KItem.of(kLabel, kList, context);
        }
        return kItem;
    }

    @Override
    public ASTNode transform(Token token) {
        return token;
    }

    @Override
    public ASTNode transform(UninterpretedConstraint uninterpretedConstraint) {
        boolean changed = false;
        UninterpretedConstraint transformedUninterpretedConstraint = new UninterpretedConstraint();
        for (UninterpretedConstraint.Equality equality : uninterpretedConstraint.equalities()) {
            Term transformedLHS = (Term) equality.leftHandSide().accept(this);
            Term transformedRHS = (Term) equality.rightHandSide().accept(this);
            changed = changed || transformedLHS != equality.leftHandSide()
                    || transformedRHS != equality.rightHandSide();
            transformedUninterpretedConstraint.add(transformedLHS, transformedRHS);
        }
        return changed ? transformedUninterpretedConstraint : uninterpretedConstraint;
    }

    @Override
    public ASTNode transform(UninterpretedToken uninterpretedToken) {
        return transform((Token) uninterpretedToken);
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        return transform((Token) bitVector);
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
    public ASTNode transform(StringToken stringToken) {
        return transform((Token) stringToken);
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
        List<Term> items = transformList(kList.getContents());

        if (kList.hasFrame()) {
            Variable frame;
            Term transformedFrame = (Term) kList.frame().accept(this);

            if (transformedFrame.kind() == Kind.KLIST) {
                if (transformedFrame instanceof KList) {
                    if (items == kList.getContents()) {
                        items = new ArrayList<>(items);
                    }
                    items.addAll(((KList) transformedFrame).getContents());
                    frame = ((KList) transformedFrame).hasFrame() ?
                            ((KList) transformedFrame).frame() : null;
                } else {
                    frame = (Variable) transformedFrame;
                }
            } else {
                assert transformedFrame.kind() == Kind.KITEM || transformedFrame.kind() == Kind.K;

                if (items == kList.getContents()) {
                    items = new ArrayList<>(items);
                }
                items.add(transformedFrame);
                frame = null;
            }

            if (items != kList.getContents() || frame != kList.frame()) {
                kList = new KList(items, frame);
            }
        } else {
            if (items != kList.getContents()) {
                kList = new KList(items);
            }
        }

        return kList;
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        boolean changed = false;
        // transform the contents
        List<Term> transformedItems = Lists.newArrayListWithCapacity(kSequence.size());
        for (Term term : kSequence) {
            Term transformedTerm = (Term) term.accept(this);
            if (transformedTerm != term) {
                changed = true;
            }
            transformedItems.add(transformedTerm);
        }
        
        Term transformedFrame = null;
        if (kSequence.hasFrame()) {
            Variable frame = kSequence.frame();
            transformedFrame = (Term) frame.accept(this);
            if (transformedFrame != frame) {
                changed = true;
            }
        }
        
        if (!changed) {
            return kSequence;
        } else {
            KSequence transformedKSeq = KSequence.of(transformedItems, transformedFrame);
            
            if (!transformedKSeq.hasFrame() && transformedKSeq.size() == 1) {
                return transformedKSeq.get(0);
            } else {
                return transformedKSeq;
            }
        }
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        Term list = (Term) listLookup.list().accept(this);
        Term key = (Term) listLookup.key().accept(this);
        if (list != listLookup.list() || key != listLookup.key()) {
            listLookup = new ListLookup(list, key, listLookup.kind());
        }
        return listLookup;
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        Term frame = null;
        boolean change = false;
        if (builtinList.hasFrame()) {
            frame = (Term) builtinList.frame().accept(this);
            if (frame != builtinList.frame()) change = true;
        }

        ArrayList<Term> elementsLeft = new ArrayList<Term>(builtinList.elementsLeft().size());
        for (Term entry : builtinList.elementsLeft()) {
            ASTNode newEntry = entry.accept(this);
            if (newEntry != entry) change = true;
            if (newEntry != null) elementsLeft.add((Term) newEntry);
        }
        ArrayList<Term> elementsRight = new ArrayList<Term>(builtinList.elementsRight().size());
        for (Term entry : builtinList.elementsRight()) {
            ASTNode newEntry = entry.accept(this);
            if (newEntry != entry) change = true;
            if (newEntry != null) elementsRight.add((Term) newEntry);
        }
        if (! change) return  builtinList;
        return BuiltinList.of(frame, builtinList.removeLeft(), builtinList.removeRight(), elementsLeft, elementsRight);
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        boolean changed = false;
        BuiltinMap.Builder builder = BuiltinMap.builder();
        
        for (Map.Entry<Term, Term> entry : builtinMap) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);
            
            // first time encounter a changed entry
            if (!changed && (key != entry.getKey() || value != entry.getValue())) {
                changed = true;
                // copy previous entries into the BuiltinMap being built
                for (Map.Entry<Term, Term> copy : builtinMap) {
                    if (copy.equals(entry)) {
                        // cannot rely on reference identity check here
                        break;
                    }
                    builder.put(copy.getKey(), copy.getValue());
                }
            }
            
            if (changed) {
                builder.put(key, value);
            }
        }
        
        // at this point, if changed is false, the BuiltinMap being built is still empty
        if (builtinMap.hasFrame()) {
            Variable oldFrame = builtinMap.frame();
            Term transformedFrame = (Term) oldFrame.accept(this);
            if (transformedFrame != oldFrame) {
                if (!changed) {
                    // the only change is the frame
                    changed = true;
                    builder.setEntriesAs(builtinMap);
                }
                builder.concat(transformedFrame);
            } else {
                builder.setFrame(oldFrame);
            }
        } else {
            // do nothing; if changed == true then all entries are already
            // copied; if changed == false then we will simply return the
            // original map later
        }
        
        return changed ? builder.build() : builtinMap;
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        BuiltinSet transformedSet = null;
        if (builtinSet.hasFrame()) {
            Term frame = (Term) builtinSet.frame().accept(this);
            if (frame != builtinSet.frame()) {
                transformedSet = BuiltinSet.of(Collections.<Term>emptySet(), frame);
            }
        }

        for(Term entry : builtinSet.elements()) {
            Term key = (Term) entry.accept(this);

            if (transformedSet == null && (key != entry)) {
                if (builtinSet.hasFrame()) {
                    transformedSet = new BuiltinSet(builtinSet.frame());
                } else {
                    transformedSet = new BuiltinSet();
                }
                for(Term copyEntry : builtinSet.elements()) {
                    if (copyEntry.equals(entry)) {
                        break;
                    }
                    transformedSet.add(copyEntry);
                }
            }

            if (transformedSet != null) {
                transformedSet.add(key);
            }
        }

        if (transformedSet != null) {
            return transformedSet;
        } else {
            return builtinSet;
        }
    }

    @Override
    public ASTNode transform(MapKeyChoice mapKeyChoice) {
        Term map = (Term) mapKeyChoice.map().accept(this);
        if (map != mapKeyChoice.map()) {
            mapKeyChoice = new MapKeyChoice(map);
        }
        return mapKeyChoice;
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        Term map = (Term) mapLookup.map().accept(this);
        Term key = (Term) mapLookup.key().accept(this);
        if (map != mapLookup.map() || key != mapLookup.key()) {
            mapLookup = new MapLookup(map, key, mapLookup.kind());
        }
        return mapLookup;

    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
//        System.out.println("Map: "+(Term)mapUpdate.map().accept(this));
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

        if (set != setUpdate.base() || removeSet != setUpdate.removeSet()) {
            setUpdate = new SetUpdate(set, removeSet);
        }

        return setUpdate;
    }

    @Override
    public ASTNode transform(SetElementChoice setElementChoice) {
        Term set = (Term) setElementChoice.set().accept(this);
        if (set != setElementChoice.set()) {
            setElementChoice = new SetElementChoice(set);
        }
        return setElementChoice;
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
    public ASTNode transform(Rule rule) {
        Term processedLeftHandSide = (Term) rule.leftHandSide().accept(this);
        Term processedRightHandSide = (Term) rule.rightHandSide().accept(this);
        List<Term> processedRequires = new ArrayList<Term>(rule.requires().size());
        for (Term conditionItem : rule.requires()) {
            processedRequires.add((Term) conditionItem.accept(this));
        }
        List<Term> processedEnsures = new ArrayList<Term>(rule.ensures().size());
        for (Term conditionItem : rule.ensures()) {
            processedEnsures.add((Term) conditionItem.accept(this));
        }
        List<Variable> processedFreshVariables = new ArrayList<Variable>(
                rule.freshVariables().size());
        for (Variable variable : rule.freshVariables()) {
            processedFreshVariables.add((Variable) variable.accept(this));
        }
        UninterpretedConstraint processedLookups
                = (UninterpretedConstraint) rule.lookups().accept(this);
        
        Map<String, Term> processedLhsOfReadCell = null;
        Map<String, Term> processedRhsOfWriteCell = null;
        if (rule.isCompiledForFastRewriting()) {
            processedLhsOfReadCell = new HashMap<>();
            for (Map.Entry<String, Term> entry : rule.lhsOfReadCell().entrySet()) {
                processedLhsOfReadCell.put(entry.getKey(), (Term) entry.getValue().accept(this));
            }
            processedRhsOfWriteCell = new HashMap<>();
            for (Map.Entry<String, Term> entry : rule.rhsOfWriteCell().entrySet()) {
                processedRhsOfWriteCell.put(entry.getKey(), (Term) entry.getValue().accept(this));
            }
        }

        if (processedLeftHandSide != rule.leftHandSide()
                || processedRightHandSide != rule.rightHandSide()
                || processedRequires.equals(rule.requires())
                || processedEnsures.equals(rule.ensures())
                || processedFreshVariables.equals(rule.freshVariables())
                || processedLookups != rule.lookups()) {
            return new Rule(
                    rule.label(),
                    processedLeftHandSide,
                    processedRightHandSide,
                    processedRequires,
                    processedEnsures,
                    processedFreshVariables,
                    processedLookups,
                    rule.isCompiledForFastRewriting(),
                    processedLhsOfReadCell,
                    processedRhsOfWriteCell,
                    rule.cellsToCopy(),
                    rule.instructions(),
                    rule.getAttributes(),
                    definition);
        } else {
            return rule;
        }
    }

    @Override
    public ASTNode transform(SymbolicConstraint symbolicConstraint) {
        SymbolicConstraint transformedSymbolicConstraint = new SymbolicConstraint(context);

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
    
    @Override
    public ASTNode transform(BuiltinMgu mgu) {
        SymbolicConstraint transformedConstraint = (SymbolicConstraint) mgu.constraint().accept(this);
        if (transformedConstraint == mgu.constraint()) {
            return BuiltinMgu.of(transformedConstraint, context);
        } else {
            return mgu;
        }
    }

    protected List<Term> transformList(List<Term> list) {
        // TODO(YilongL): avoid using index number to traverse the list, there
        // is no guarantee that the underlying list is a random access list
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
