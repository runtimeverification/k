// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;


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
        CellCollection.Builder builder = CellCollection.builder(context.definition().context());
        for (Cell<?> cell : cellCollection.cellMap().values()) {
            Cell<?> transformedCell = (Cell<?>) cell.accept(this);
            builder.add(transformedCell);
            changed = changed || cell != transformedCell;
        }
        for (Term term : cellCollection.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            builder.concatenate(transformedTerm);
            changed = changed || term != transformedTerm;
        }
        return changed ? builder.build() : cellCollection;
    }

    @Override
    public ASTNode transform(Collection collection) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(ConstrainedTerm constrainedTerm) {
        Term term = (Term) constrainedTerm.term().accept(this);
        SymbolicConstraint lookups = (SymbolicConstraint) constrainedTerm.lookups().accept(this);
        SymbolicConstraint constraint = (SymbolicConstraint) constrainedTerm.constraint().accept(this);
        if (term != constrainedTerm.term()
                || lookups != constrainedTerm.lookups()
                || constraint != constrainedTerm.constraint()) {
            constrainedTerm = new ConstrainedTerm(term, lookups, constraint, context);
        }
        return constrainedTerm;
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
        UninterpretedConstraint.Builder builder = UninterpretedConstraint.builder();
        for (UninterpretedConstraint.Equality equality : uninterpretedConstraint.equalities()) {
            Term transformedLHS = (Term) equality.leftHandSide().accept(this);
            Term transformedRHS = (Term) equality.rightHandSide().accept(this);
            changed = changed || transformedLHS != equality.leftHandSide()
                    || transformedRHS != equality.rightHandSide();
            builder.add(transformedLHS, transformedRHS);
        }
        return changed ? builder.build() : uninterpretedConstraint;
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
        boolean changed = false;
        // transform the contents
        KList.Builder builder = KList.builder();
        for (Term term : kList) {
            Term transformedTerm = (Term) term.accept(this);
            if (transformedTerm != term) {
                changed = true;
            }
            builder.concatenate(transformedTerm);
        }

        if (kList.hasFrame()) {
            Variable frame = kList.frame();
            Term transformedFrame = (Term) frame.accept(this);
            if (transformedFrame != frame) {
                changed = true;
            }
            builder.concatenate(transformedFrame);
        }

        if (!changed) {
            return kList;
        } else {
            return builder.build();
        }
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        boolean changed = false;
        // transform the contents
        KSequence.Builder builder = KSequence.builder();
        for (Term term : kSequence) {
            Term transformedTerm = (Term) term.accept(this);
            if (transformedTerm != term) {
                changed = true;
            }
            builder.concatenate(transformedTerm);
        }

        if (kSequence.hasFrame()) {
            Variable frame = kSequence.frame();
            Term transformedFrame = (Term) frame.accept(this);
            if (transformedFrame != frame) {
                changed = true;
            }
            builder.concatenate(transformedFrame);
        }

        if (!changed) {
            return kSequence;
        } else {
            return builder.build();
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
    public ASTNode transform(ListUpdate listUpdate) {
        Term list = (Term) listUpdate.list().accept(this);
        if (list != listUpdate.list()) {
            listUpdate = new ListUpdate(list, listUpdate.removeLeft(), listUpdate.removeRight());
        }
        return listUpdate;
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        boolean changed = false;
        BuiltinList.Builder builder = BuiltinList.builder();
        for (Term term : builtinList.elementsLeft()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.addItem(transformedTerm);
        }
        for (Term term : builtinList.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.concatenate(transformedTerm);
        }
        for (Term term : builtinList.elementsRight()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.addItem(transformedTerm);
        }
        return changed ? builder.build() : builtinList;
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        boolean changed = false;
        BuiltinMap.Builder builder = BuiltinMap.builder();

        for (Map.Entry<Term, Term> entry : builtinMap.getEntries().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);

            // first time encounter a changed entry
            if (!changed && (key != entry.getKey() || value != entry.getValue())) {
                changed = true;
                // copy previous entries into the BuiltinMap being built
                for (Map.Entry<Term, Term> copy : builtinMap.getEntries().entrySet()) {
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
        /* special case for maps composed only of entries */
        if (builtinMap.isConcreteCollection()) {
            return changed ? builder.build() : builtinMap;
        }

        if (!changed) {
            builder.putAll(builtinMap.getEntries());
        }

        for (Term term : builtinMap.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.concatenate(transformedTerm);
        }

        return changed ? builder.build() : builtinMap;
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        boolean changed = false;
        BuiltinSet.Builder builder = BuiltinSet.builder();
        for(Term element : builtinSet.elements()) {
            Term transformedElement = (Term) element.accept(this);
            builder.add(transformedElement);
            changed = changed || (transformedElement != element);
        }
        for (Term term : builtinSet.baseTerms()) {
            Term transformedTerm = (Term) term.accept(this);
            changed = changed || (transformedTerm != term);
            builder.concatenate(transformedTerm);
        }
        return changed ? builder.build() : builtinSet;
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
        Set<Variable> processedFreshVariables = new HashSet<Variable>(
                rule.freshVariables().size());
        for (Variable variable : rule.freshVariables()) {
            processedFreshVariables.add((Variable) variable.accept(this));
        }
        UninterpretedConstraint processedLookups
                = (UninterpretedConstraint) rule.lookups().accept(this);

        Map<CellLabel, Term> processedLhsOfReadCell = null;
        Map<CellLabel, Term> processedRhsOfWriteCell = null;
        if (rule.isCompiledForFastRewriting()) {
            processedLhsOfReadCell = new HashMap<>();
            for (Map.Entry<CellLabel, Term> entry : rule.lhsOfReadCell().entrySet()) {
                processedLhsOfReadCell.put(entry.getKey(), (Term) entry.getValue().accept(this));
            }
            processedRhsOfWriteCell = new HashMap<>();
            for (Map.Entry<CellLabel, Term> entry : rule.rhsOfWriteCell().entrySet()) {
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
                    rule,
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

}
