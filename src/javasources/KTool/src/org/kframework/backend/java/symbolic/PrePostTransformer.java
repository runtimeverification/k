package org.kframework.backend.java.symbolic;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Multimap;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.kil.Collection;
import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.*;


/**
 * Performs transformation which includes pre-processing and post-processing.
 * <p><br>
 * Transformation on a given node is performed in three steps:
 * <li>pre-processing that node;
 * <li>applying transformation recursively on its children;
 * <li>post-processing that node.
 * 
 * @author AndreiS
 */
public abstract class PrePostTransformer implements Transformer {

    protected final TermContext context;
    protected final Definition definition;

    /**
     * Returns the {@code CombinedLocalTransformer} used for pre-processing.
     */
    public CombinedLocalTransformer getPreTransformer() {
        return preTransformer;
    }

    public void setPreTransformer(CombinedLocalTransformer preTransformer) {
        this.preTransformer = preTransformer;
    }

    /**
     * Returns the {@code CombinedLocalTransformer} used for post-processing.
     */
    public CombinedLocalTransformer getPostTransformer() {
        return postTransformer;
    }

    public void setPostTransformer(CombinedLocalTransformer postTransformer) {
        this.postTransformer = postTransformer;
    }

    protected CombinedLocalTransformer preTransformer = new CombinedLocalTransformer();
    protected CombinedLocalTransformer postTransformer = new CombinedLocalTransformer();

	public PrePostTransformer(TermContext context) {
		this.context = context;
        this.definition = context.definition();
	}

    public PrePostTransformer(Definition definition) {
        this(new TermContext(definition));
    }

    public PrePostTransformer() {
        this.context = null;
        this.definition = null;
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public ASTNode transform(Cell cell) {
        ASTNode astNode = cell.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Cell : "preTransformer should not modify type";
        cell = (Cell) astNode;
        Term content = (Term) cell.getContent().accept(this);
        if (content != cell.getContent()) {
            cell = new Cell<Term>(cell.getLabel(), content);
        }
        return cell.accept(postTransformer);
    }

    @Override
    public ASTNode transform(CellCollection cellCollection) {
        ASTNode astNode = cellCollection.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof CellCollection : "preTransformer should not modify type";
        cellCollection = (CellCollection) astNode;
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
            boolean isStar = cellCollection.isStar();
            Variable frame;
            Term transformedFrame = (Term) cellCollection.frame().accept(this);
            if (transformedFrame instanceof CellCollection) {
                isStar = isStar || ((CellCollection) transformedFrame).isStar();
                if (cells == cellCollection.cellMap()) {
                    cells = HashMultimap.create(cellCollection.cellMap());
                }
                cells.putAll(((CellCollection) transformedFrame).cellMap());
                frame = ((CellCollection) transformedFrame).hasFrame() ?
                        ((CellCollection) transformedFrame).frame() : null;
            } else {
                frame = (Variable) transformedFrame;
            }

            if (cells != cellCollection.cellMap() || frame != cellCollection.frame()) {
                cellCollection = new CellCollection(cells, frame, isStar);
            }
        } else {
            if (cells != cellCollection.cellMap()) {
                cellCollection = new CellCollection(cells, cellCollection.isStar());
            }
        }

        return cellCollection.accept(postTransformer);
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
        ASTNode astNode = kLabelConstant.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabelConstant : "preTransformer should not modify type";
        kLabelConstant = (KLabelConstant) astNode;
        return kLabelConstant.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KLabelFreezer kLabelFreezer) {
        ASTNode astNode = kLabelFreezer.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabelFreezer : "preTransformer should not modify type";
        kLabelFreezer = (KLabelFreezer) astNode;
        Term term = (Term) kLabelFreezer.term().accept(this);
        if (term != kLabelFreezer.term()) {
            kLabelFreezer = new KLabelFreezer(term);
        }
        return kLabelFreezer.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Hole hole) {
        ASTNode astNode = hole.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Hole : "preTransformer should not modify type";
        hole = (Hole) astNode;
        return hole.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KLabelInjection kLabelInjection) {
        ASTNode astNode = kLabelInjection.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabelInjection : "preTransformer should not modify type";
        kLabelInjection = (KLabelInjection) astNode;
        Term term = (Term) kLabelInjection.term().accept(this);
        if (term != kLabelInjection.term()) {
            kLabelInjection = new KLabelInjection(term);
        }
        return kLabelInjection.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        ASTNode astNode = kItem.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KItem : "preTransformer should not modify type";
        kItem = (KItem) astNode;
        KLabel kLabel = (KLabel) kItem.kLabel().accept(this);
        KList kList = (KList) kItem.kList().accept(this);
        if (kLabel != kItem.kLabel() || kList != kItem.kList()) {
            kItem = new KItem(kLabel, kList, context.definition().context());
        }
        return kItem.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Token token) {
        ASTNode astNode = token.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Token : "preTransformer should not modify type";
        token = (Token) astNode;
        return token.accept(postTransformer);
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
    public ASTNode transform(Int32Token intToken) {
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
        ASTNode astNode = kLabel.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KLabel : "preTransformer should not modify type";
        kLabel = (KLabel) astNode;
        return kLabel.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KList kList) {
        ASTNode astNode = kList.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KList : "preTransformer should not modify type";
        kList = (KList) astNode;
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

        return kList.accept(postTransformer);
    }

    @Override
    public ASTNode transform(KSequence kSequence) {
        ASTNode astNode = kSequence.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof KSequence : "preTransformer should not modify type";
        kSequence = (KSequence) astNode;
        List<Term> items = transformList(kSequence.getItems());

        if (kSequence.hasFrame()) {
            Variable frame;
            Term transformedFrame = (Term) kSequence.frame().accept(this);

            if (transformedFrame.kind() == Kind.K) {
                if (transformedFrame instanceof KSequence) {
                    if (items == kSequence.getItems()) {
                        items = new ArrayList<Term>(items);
                    }
                    items.addAll(((KSequence) transformedFrame).getItems());
                    frame = ((KSequence) transformedFrame).hasFrame() ?
                            ((KSequence) transformedFrame).frame() : null;
                } else if (transformedFrame instanceof KCollectionFragment) {
                    if (items == kSequence.getItems()) {
                        items = new ArrayList<Term>(items);
                    }
                    Iterables.addAll(items, (KCollectionFragment) transformedFrame);
                    frame = ((KCollectionFragment) transformedFrame).hasFrame() ?
                            ((KCollectionFragment) transformedFrame).frame() : null;
                } else {
                    frame = (Variable) transformedFrame;
                }
            } else {
                assert transformedFrame.kind() == Kind.KITEM;

                if (items == kSequence.getItems()) {
                    items = new ArrayList<Term>(items);
                }
                items.add(transformedFrame);
                frame = null;
            }

            if (items != kSequence.getItems() || frame != kSequence.frame()) {
                kSequence = new KSequence(ImmutableList.<Term>copyOf(items), frame);
            }
        } else {
            if (items != kSequence.getItems()) {
                kSequence = new KSequence(ImmutableList.<Term>copyOf(items));
            }
        }

        if (kSequence.hasFrame() || kSequence.size() != 1) {
            return kSequence.accept(postTransformer);
        } else {
            return kSequence.get(0);
        }
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        ASTNode astNode = listLookup.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof ListLookup : "preTransformer should not modify type";
        listLookup = (ListLookup) astNode;
        Term list = (Term) listLookup.list().accept(this);
        Term key = (Term) listLookup.key().accept(this);
        if (list != listLookup.list() || key != listLookup.key()) {
            listLookup = new ListLookup(list, key);
        }
        return listLookup.accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinList builtinList) {
        ASTNode astNode = builtinList.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinList : "preTransformer should not modify type";
        builtinList = (BuiltinList) astNode;
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
        return BuiltinList.of(frame, builtinList.removeLeft(), builtinList.removeRight(),
                elementsLeft, elementsRight).accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinMap builtinMap) {
        ASTNode astNode = builtinMap.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinMap : "preTransformer should not modify type";
        builtinMap = (BuiltinMap) astNode;
        BuiltinMap transformedMap = null;
        if (builtinMap.hasFrame()) {
            Term frame = (Term) builtinMap.frame().accept(this);
            if (frame != builtinMap.frame()) {
                transformedMap = BuiltinMap.of(Collections.<Term, Term>emptyMap(), frame);
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
            builtinMap = transformedMap;
        }
        return builtinMap.accept(postTransformer);
    }

    @Override
    public ASTNode transform(BuiltinSet builtinSet) {
        ASTNode astNode = builtinSet.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof BuiltinSet : "preTransformer should not modify type";
        builtinSet = (BuiltinSet) astNode;
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
            builtinSet = transformedSet;
        }
        return builtinSet.accept(postTransformer);
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        ASTNode astNode = mapLookup.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof MapLookup : "preTransformer should not modify type";
        mapLookup = (MapLookup) astNode;
        Term map = (Term) mapLookup.map().accept(this);
        Term key = (Term) mapLookup.key().accept(this);
        if (map != mapLookup.map() || key != mapLookup.key()) {
            mapLookup = new MapLookup(map, key);
        }
        return mapLookup.accept(postTransformer);

    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        ASTNode astNode = mapUpdate.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof MapUpdate : "preTransformer should not modify type";
        mapUpdate = (MapUpdate) astNode;
//        System.out.println("Map: "+(Term)mapUpdate.map().accept(this));
        Term map = (Term) mapUpdate.map().accept(this);
        Set<Term> removeSet = null;
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
        for(Map.Entry<Term, Term> entry : mapUpdate.updateMap().entrySet()) {
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

        return mapUpdate.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        ASTNode astNode = setUpdate.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SetUpdate : "preTransformer should not modify type";
        setUpdate = (SetUpdate) astNode;
        Term set = (Term) setUpdate.base().accept(this);

        Set<Term> removeSet = null;
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

        return setUpdate.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        ASTNode astNode = setLookup.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SetLookup : "preTransformer should not modify type";
        setLookup = (SetLookup) astNode;
        Term base = (Term) setLookup.base().accept(this);
        Term key = (Term) setLookup.key().accept(this);
        if (base != setLookup.base() || key != setLookup.key()) {
            setLookup = new SetLookup(base, key);
        }
        return setLookup.accept(postTransformer);
    }

    @Override
    public ASTNode transform(MetaVariable metaVariable) {
        return transform((Token) metaVariable);
    }

    @Override
    public ASTNode transform(Rule rule) {
        ASTNode astNode = rule.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Rule : "preTransformer should not modify type";
        rule = (Rule) astNode;
        Term processedLeftHandSide = (Term) rule.leftHandSide().accept(this);
        Term processedRightHandSide = (Term) rule.rightHandSide().accept(this);
        List<Term> processedCondition = new ArrayList<Term>(rule.condition().size());
        for (Term conditionItem : rule.condition()) {
            processedCondition.add((Term) conditionItem.accept(this));
        }
        List<Variable> processedFreshVariables = new ArrayList<Variable>(
                rule.freshVariables().size());
        for (Variable variable : rule.freshVariables()) {
            processedFreshVariables.add((Variable) variable.accept(this));
        }
        UninterpretedConstraint processedLookups
                = (UninterpretedConstraint) rule.lookups().accept(this);

        if (processedLeftHandSide != rule.leftHandSide()
                || processedRightHandSide != rule.rightHandSide()
                || !processedCondition.equals(rule.condition())
                || !processedFreshVariables.equals(rule.freshVariables())
                || processedLookups != rule.lookups()) {
            rule = new Rule(
                    processedLeftHandSide,
                    processedRightHandSide,
                    processedCondition,
                    processedFreshVariables,
                    processedLookups,
                    rule.getAttributes());
        }
        return rule.accept(postTransformer);
    }

    @Override
    public ASTNode transform(SymbolicConstraint symbolicConstraint) {
        ASTNode astNode = symbolicConstraint.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof SymbolicConstraint : "preTransformer should not modify type";
        symbolicConstraint = (SymbolicConstraint) astNode;
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

        return transformedSymbolicConstraint.accept(postTransformer);
    }

    @Override
    public ASTNode transform(UninterpretedConstraint uninterpretedConstraint) {
        ASTNode astNode = uninterpretedConstraint.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof UninterpretedConstraint : "preTransformer should not modify type";
        uninterpretedConstraint = (UninterpretedConstraint) astNode;

        UninterpretedConstraint transformedUninterpretedConstraint = new UninterpretedConstraint();
        for (UninterpretedConstraint.Equality equality : uninterpretedConstraint.equalities()) {
            transformedUninterpretedConstraint.add(
                    (Term) equality.leftHandSide().accept(this),
                    (Term) equality.rightHandSide().accept(this));
        }

        return transformedUninterpretedConstraint.accept(postTransformer);
    }

    @Override
    public ASTNode transform(Term node) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(Variable variable) {
        ASTNode astNode = variable.accept(preTransformer);
        if (astNode instanceof DoneTransforming) {
            return ((DoneTransforming) astNode).getContents();
        }
        assert astNode instanceof Variable : "preTransformer should not modify type";
        variable = (Variable) astNode;
        return variable.accept(postTransformer);
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

    protected class DoneTransforming extends ASTNode {
        DoneTransforming(ASTNode node) {
            contents = node;
        }

        @Override
        public ASTNode shallowCopy() {
            throw new UnsupportedOperationException();
        }

        public ASTNode getContents() {
            return contents;
        }

        private final ASTNode contents;

        @Override
        public ASTNode accept(org.kframework.kil.visitors.Transformer transformer) throws TransformerException {
            throw new UnsupportedOperationException();
        }

        @Override
        public void accept(Visitor visitor) {
            throw new UnsupportedOperationException();
        }
    }
}
