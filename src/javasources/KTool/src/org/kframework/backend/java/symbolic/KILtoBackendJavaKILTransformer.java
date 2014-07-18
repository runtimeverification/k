// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import static org.kframework.kil.KLabelConstant.ANDBOOL_KLABEL;
import static org.kframework.kil.KLabelConstant.BOOL_ANDBOOL_KLABEL;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinMgu;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemProjection;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.ListLookup;
import org.kframework.backend.java.kil.MapKeyChoice;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.SetElementChoice;
import org.kframework.backend.java.kil.SetLookup;
import org.kframework.backend.java.kil.SetUpdate;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.GenericToken;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.TermComment;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;


/**
 * Convert a term from the KIL representation into the Java Rewrite engine internal representation.
 *
 * @author AndreiS
 */
public class KILtoBackendJavaKILTransformer extends CopyOnWriteTransformer {

    private boolean freshRules;
    private Definition definition = null;

    /**
     * Maps variables representing concrete collections to their sizes. This
     * field is set at the beginning of
     * {@link #visit(org.kframework.kil.Rule)} and reset before that method
     * returns. Moreover, it is only used in
     * {@link #visit(org.kframework.kil.Variable)} when transforming
     * {@code Variable}s inside that {@code Rule}.
     */
    private Map<org.kframework.kil.Variable, Integer> concreteCollectionSize
            = Collections.emptyMap();
    private GlobalContext globalContext;

    public KILtoBackendJavaKILTransformer(Context context) {
        super("Transform KIL into java backend KIL", context);
        freshRules = false;
    }

    public KILtoBackendJavaKILTransformer(Context context, boolean freshRules) {
        this(context);
        this.freshRules = freshRules;
    }

    public Definition transformDefinition(org.kframework.kil.Definition node) {
        Definition transformedDef = (Definition) this.visitNode(node);
        GlobalContext transformedDefGlobalContext = new GlobalContext(transformedDef, null);

        Definition expandedDefinition = new MacroExpander(TermContext.of(transformedDefGlobalContext)).processDefinition();
        return evaluateDefinition(new GlobalContext(expandedDefinition, null));
    }

    public Rule transformRule(org.kframework.kil.Rule node, Definition definition) {
        this.definition = definition;
        this.globalContext = new GlobalContext(definition, null);

        Rule rule = null;
        try {
            rule = new MacroExpander(TermContext.of(globalContext)).processRule((Rule) this.visitNode(node));
        } finally {
            this.definition = null;
            this.globalContext = null;
        }

        return rule;
    }

    public Term transformTerm(org.kframework.kil.Term node, Definition definition) {
        this.definition = definition;
        this.globalContext = new GlobalContext(definition, null);

        Term term = null;
        try {
            term = new MacroExpander(TermContext.of(globalContext)).processTerm((Term) this.visitNode(node));
        } finally {
            this.definition = null;
            this.globalContext = null;
        }

        return term;
    }

    @Override
    public ASTNode visit(org.kframework.kil.KApp node, Void _)  {
        if (node.getLabel() instanceof org.kframework.kil.Token) {
            if (node.getLabel() instanceof BoolBuiltin) {
                return BoolToken.of(((BoolBuiltin) node.getLabel()).booleanValue());
            } else if (node.getLabel() instanceof IntBuiltin) {
                return IntToken.of(((IntBuiltin) node.getLabel()).bigIntegerValue());
            } else if (node.getLabel() instanceof StringBuiltin) {
                return StringToken.of(((StringBuiltin) node.getLabel()).stringValue());
            } else if (node.getLabel() instanceof FloatBuiltin) {
                return FloatToken.of(
                        ((FloatBuiltin) node.getLabel()).bigFloatValue(),
                        ((FloatBuiltin) node.getLabel()).exponent());
            } else if (node.getLabel() instanceof GenericToken) {
                return UninterpretedToken.of(
                        Sort.of(((GenericToken) node.getLabel()).tokenSort()),
                        ((GenericToken) node.getLabel()).value());
            } else {
                assert false : "unsupported Token " + node.getLabel();
            }
        }

        Term kLabel = (Term) this.visitNode(node.getLabel());
        Term kList = (Term) this.visitNode(node.getChild());
        if (kList instanceof Variable) {
            kList = new KList((Variable) kList);
        }
        return KItem.of(kLabel, kList, TermContext.of(globalContext));
    }

    @Override
    public ASTNode visit(org.kframework.kil.KItemProjection node, Void _)  {
        return new KItemProjection(Kind.of(Sort.of(node.projectedKind())), (Term) this.visitNode(node.getTerm()));
    }

    @Override
    public ASTNode visit(org.kframework.kil.KLabelConstant node, Void _)  {
        return KLabelConstant.of(node.getLabel(), definition);
    }

    @Override
    public ASTNode visit(org.kframework.kil.KLabelInjection node, Void _)  {
        return new KLabelInjection((Term) this.visitNode(node.getTerm()));
    }

    @Override
    public ASTNode visit(org.kframework.kil.KInjectedLabel node, Void _)  {
        Term term = (Term) this.visitNode(node.getTerm());
        return new KLabelInjection(term);
    }

    @Override
    public ASTNode visit(org.kframework.kil.FreezerLabel node, Void _)  {
        Term term = (Term) this.visitNode(node.getTerm());
        return new KLabelFreezer(term);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Hole node, Void _)  {
        return Hole.HOLE;
    }

    @Override
    public ASTNode visit(org.kframework.kil.FreezerHole node, Void _)  {
        return Hole.HOLE;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Token node, Void _)  {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode visit(org.kframework.kil.KSequence node, Void _)  {
        List<org.kframework.kil.Term> list = new ArrayList<org.kframework.kil.Term>();
        KILtoBackendJavaKILTransformer.flattenKSequence(list, node.getContents());

        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(org.kframework.kil.KSorts.K)) {
            variable = (Variable) this.visitNode(list.remove(list.size() - 1));
        }

        List<Term> items = Lists.newArrayListWithCapacity(list.size());
        for (org.kframework.kil.Term term : list) {
            items.add((Term) this.visitNode(term));
        }

        return new KSequence(items, variable);
    }

    @Override
    public ASTNode visit(org.kframework.kil.KList node, Void _)  {
        List<org.kframework.kil.Term> list = new ArrayList<org.kframework.kil.Term>();
        KILtoBackendJavaKILTransformer.flattenKList(list, node.getContents());

        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(org.kframework.kil.KSorts.KLIST)) {
            variable = (Variable) this.visitNode(list.remove(list.size() - 1));
        }

        List<Term> items = Lists.newArrayListWithCapacity(list.size());
        for (org.kframework.kil.Term term : list) {
            items.add((Term) this.visitNode(term));
        }

        return new KList(items, variable);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Cell node, Void _)  {
        if (node.getContents() instanceof org.kframework.kil.Bag) {
            CellCollection cellCollection = (CellCollection) this.visitNode(node.getContents());
            return new Cell<CellCollection>(node.getLabel(), cellCollection);
        } else if (node.getContents() instanceof org.kframework.kil.Cell) {
            Multimap<String, Cell> cells = ArrayListMultimap.create();
            Cell<?> cell = (Cell<?>) this.visitNode(node.getContents());
            cells.put(cell.getLabel(), cell);

            return new Cell<CellCollection>(node.getLabel(),
                    new CellCollection(cells, context));
        } else {
            Term content = (Term) this.visitNode(node.getContents());

            if (content instanceof KItem) {
                return new Cell<KItem>(node.getLabel(), (KItem) content);
            } else if (content instanceof Token) {
                return new Cell<Token>(node.getLabel(), (Token) content);
            } else if (content instanceof KSequence) {
                return new Cell<KSequence>(node.getLabel(), (KSequence) content);
            } else if (content instanceof KList) {
                return new Cell<KList>(node.getLabel(), (KList) content);
            } else if (content instanceof BuiltinList) {
                return new Cell<BuiltinList>(node.getLabel(), (BuiltinList) content);
//            } else if (content instanceof ListUpdate) {
//                return new Cell<ListUpdate>(node.getLabel(), (ListUpdate) content);
            } else if (content instanceof BuiltinSet) {
                return new Cell<BuiltinSet>(node.getLabel(), (BuiltinSet) content);
            } else if (content instanceof SetUpdate) {
                return new Cell<SetUpdate>(node.getLabel(), (SetUpdate) content);
            } else if (content instanceof BuiltinMap) {
                return new Cell<BuiltinMap>(node.getLabel(), (BuiltinMap) content);
            } else if (content instanceof MapUpdate) {
                return new Cell<MapUpdate>(node.getLabel(), (MapUpdate) content);
            } else if (content instanceof Variable) {
                return new Cell<Term>(node.getLabel(), content);
            } else if (content instanceof KItemProjection) {
                return new Cell<KItemProjection>(node.getLabel(), (KItemProjection) content);
            } else if (content instanceof BuiltinMgu) {
                return new Cell<BuiltinMgu>(node.getLabel(), (BuiltinMgu) content);
            } else {
                throw new RuntimeException();
            }
        }
    }

    @Override
    public ASTNode visit(org.kframework.kil.Bag node, Void _) {
        List<org.kframework.kil.Term> contents = new ArrayList<org.kframework.kil.Term>();
        org.kframework.kil.Bag.flatten(contents,
                ((org.kframework.kil.Bag) node).getContents());

        Multimap<String, Cell> cells = ArrayListMultimap.create();
        List<Variable> baseTerms = Lists.newArrayList();
        for (org.kframework.kil.Term term : contents) {
            if (term instanceof TermComment) {
                continue;
            }
            if (term instanceof org.kframework.kil.Cell) {
                Cell<?> cell = (Cell<?>) this.visitNode(term);
                cells.put(cell.getLabel(), cell);
            } else if (term instanceof org.kframework.kil.Variable
                    && (term.getSort().equals(org.kframework.kil.KSorts.BAG))) {
                baseTerms.add((Variable) this.visitNode(term));
            } else {
                throw new RuntimeException();
            }
        }

        return new CellCollection(cells, baseTerms, context);
    }

    @Override
    public ASTNode visit(org.kframework.kil.ListBuiltin node, Void _)  {
        ArrayList<Term> elementsLeft = new ArrayList<Term>(node.elementsLeft().size());
        for (org.kframework.kil.Term entry : node.elementsLeft()) {
            Term newEntry = (Term) this.visitNode(entry);
            elementsLeft.add(newEntry);
        }

        ArrayList<Term> elementsRight = new ArrayList<Term>(node.elementsRight().size());
        for (org.kframework.kil.Term entry : node.elementsRight()) {
            Term newEntry = (Term) this.visitNode(entry);
            elementsRight.add(newEntry);
        }

        ArrayList<Term> baseTerms = new ArrayList<>(node.baseTerms().size());
        for (org.kframework.kil.Term term : node.baseTerms()) {
            baseTerms.add((Term) this.visitNode(term));
        }

        Term base = null;
        if (node.hasViewBase()) {
            base = (Variable) this.visitNode(node.viewBase());
        } else {
            if (!node.baseTerms().isEmpty()) {
                if (node.baseTerms().size() == 1
                        && !( this.visitNode(node.baseTerms().iterator().next()) instanceof KItem)) {
                    base = (Term) this.visitNode(node.baseTerms().iterator().next());
                } else {
                    Term result = BuiltinList.of(
                            null,
                            0,
                            0,
                            elementsLeft,
                            new ArrayList<Term>());
                    baseTerms.add(BuiltinList.of(
                            null,
                            0,
                            0,
                            new ArrayList<Term>(),
                            elementsRight));
                    for (Term baseTerm : baseTerms) {
                        result = KItem.of(
                                KLabelConstant.of(DataStructureSort.DEFAULT_LIST_LABEL, definition),
                                new KList(ImmutableList.of(result, baseTerm)),
                                TermContext.of(globalContext));
                    }
                    return result;
                }
            }
        }
        return BuiltinList.of(base, 0, 0, elementsLeft, elementsRight);
    }

    @Override
    public ASTNode visit(org.kframework.kil.SetBuiltin node, Void _)  {
        HashSet<Term> entries = new HashSet<Term>(node.elements().size());
        for (org.kframework.kil.Term entry : node.elements()) {
            Term key = (Term) this.visitNode(entry);
            entries.add(key);
        }

        if (node.isLHSView()) {
            if (node.hasViewBase()) {
                Term base = (Term) this.visitNode(node.viewBase());
                if (base instanceof SetUpdate) {
                    SetUpdate setUpdate = (SetUpdate) base;
                    /* TODO(AndreiS): check key uniqueness */
                    return new SetUpdate(setUpdate.base(), setUpdate.removeSet());
                } else {
                    /* base instanceof Variable */
                    return new BuiltinSet(entries, (Variable) base);
                }
            } else {
                return new BuiltinSet(entries);
            }
        } else {
            ArrayList<Term> baseTerms = new ArrayList<>(node.baseTerms().size());
            for (org.kframework.kil.Term term : node.baseTerms()) {
                baseTerms.add((Term) this.visitNode(term));
            }
            baseTerms.add(new BuiltinSet(entries));

            Term result = baseTerms.get(0);
            for (int i = 1; i < baseTerms.size(); ++i) {
                result = KItem.of(
                        KLabelConstant.of(DataStructureSort.DEFAULT_SET_LABEL, definition),
                        new KList(ImmutableList.of(result, baseTerms.get(i))),
                        TermContext.of(globalContext));
            }
            return result;
        }
    }

    @Override
    public ASTNode visit(org.kframework.kil.MapBuiltin node, Void _)  {
        BuiltinMap.Builder builder = BuiltinMap.builder();
        for (Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.elements().entrySet()) {
            Term key = (Term) this.visitNode(entry.getKey());
            Term value = (Term) this.visitNode(entry.getValue());
            builder.put(key, value);
        }

        if (node.isLHSView()) {
            if (node.hasViewBase()) {
                Term base = (Term) this.visitNode(node.viewBase());
                if (base instanceof MapUpdate) {
                    MapUpdate mapUpdate = (MapUpdate) base;
                    /* TODO(AndreiS): check key uniqueness */
                    builder.putAll(mapUpdate.updateMap());
                    return new MapUpdate(mapUpdate.map(), mapUpdate.removeSet(), builder.getEntries());
                } else {
                    /* base instanceof Variable */
                    builder.setFrame((Variable) base);
                    return builder.build();
                }
            } else {
                return builder.build();
            }
        } else {
            ArrayList<Term> baseTerms = new ArrayList<>(node.baseTerms().size());
            for (org.kframework.kil.Term term : node.baseTerms()) {
                baseTerms.add((Term) this.visitNode(term));
            }
            baseTerms.add(builder.build());

            Term result = baseTerms.get(0);
            for (int i = 1; i < baseTerms.size(); ++i) {
                result = KItem.of(
                        KLabelConstant.of(DataStructureSort.DEFAULT_MAP_LABEL, definition),
                        new KList(ImmutableList.of(result, baseTerms.get(i))),
                        TermContext.of(globalContext));
            }
            return result;
        }
    }

    @Override
    public ASTNode visit(org.kframework.kil.ListUpdate node, Void _)  {
        Variable base = (Variable) this.visitNode(node.base());

        return BuiltinList.of(base, node.removeLeft().size(), node.removeRight().size(),
                Collections.<Term>emptyList(), Collections.<Term>emptyList());
    }

    @Override
    public ASTNode visit(org.kframework.kil.SetUpdate node, Void _)  {
        Variable set = (Variable) this.visitNode(node.set());

        HashSet<Term> removeSet = new HashSet<Term>(node.removeEntries().size());
        for (org.kframework.kil.Term term : node.removeEntries()) {
            removeSet.add((Term) this.visitNode(term));
        }

        return new SetUpdate(set, removeSet);
    }

     @Override
    public ASTNode visit(org.kframework.kil.MapUpdate node, Void _)  {
        Variable map = (Variable) this.visitNode(node.map());

        HashSet<Term> removeSet = new HashSet<Term>(node.removeEntries().size());
        for (org.kframework.kil.Term term : node.removeEntries().keySet()) {
            removeSet.add((Term) this.visitNode(term));
        }

        HashMap<Term, Term> updateMap = new HashMap<Term, Term>(node.updateEntries().size());
        for (Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.updateEntries().entrySet()) {
            Term key = (Term) this.visitNode(entry.getKey());
            Term value = (Term) this.visitNode(entry.getValue());
            updateMap.put(key, value);
        }

        return new MapUpdate(map, removeSet, updateMap);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Variable node, Void _)  {
        if (node.getSort().equals(org.kframework.kil.KSorts.BAG)) {
            return new Variable(node.getName(), Kind.CELL_COLLECTION.asSort());
        }

        if (node.getSort().equals(org.kframework.kil.KSorts.K)) {
            return new Variable(node.getName(), Sort.KSEQUENCE);
        }
        if (node.getSort().equals(org.kframework.kil.KSorts.KLIST)) {
            return new Variable(node.getName(), Sort.KLIST);
        }

        DataStructureSort dataStructureSort = context.dataStructureSortOf(node.getSort());
        if (dataStructureSort != null) {
            Sort sort = null;
            if (dataStructureSort.type().equals(org.kframework.kil.KSorts.LIST)) {
                sort = Sort.LIST;
            } else if (dataStructureSort.type().equals(org.kframework.kil.KSorts.MAP)) {
                sort = Sort.MAP;
            } else if (dataStructureSort.type().equals(org.kframework.kil.KSorts.SET)) {
                sort = Sort.SET;
            } else {
                assert false: "unexpected data structure " + dataStructureSort.type();
            }

            if (concreteCollectionSize.containsKey(node)) {
                return new ConcreteCollectionVariable(
                        node.getName(),
                        sort,
                        concreteCollectionSize.get(node));
            } else {
                return new Variable(node.getName(), sort);
            }
        }

        return new Variable(node.getName(), Sort.of(node.getSort()));
    }

    @Override
    public ASTNode visit(org.kframework.kil.Rule node, Void _)  {
        assert node.getBody() instanceof org.kframework.kil.Rewrite;

        concreteCollectionSize = node.getConcreteDataStructureSize();

        org.kframework.kil.Rewrite rewrite = (org.kframework.kil.Rewrite) node.getBody();
        Term leftHandSide = (Term) this.visitNode(rewrite.getLeft());
        Term rightHandSide = (Term) this.visitNode(rewrite.getRight());

        Collection<Term> requires = new ArrayList<>();
        if (node.getRequires() != null) {
            transformConjunction(requires, (Term) this.visitNode(node.getRequires()));
        }

        Collection<Term> ensures = new ArrayList<>();
        if (node.getEnsures() != null) {
            transformConjunction(requires, (Term) this.visitNode(node.getEnsures()));
        }

        UninterpretedConstraint lookups = new UninterpretedConstraint();
        for (org.kframework.kil.BuiltinLookup lookup : node.getLookups()) {
            Variable base = (Variable) this.visitNode(lookup.base());
            Term key = (Term) this.visitNode(lookup.key());
            Kind kind;
            switch (lookup.kind()) {
                case KItem:
                    kind = Kind.KITEM;
                    break;
                case K:
                    kind = Kind.K;
                    break;
                case KList:
                    kind = Kind.KLIST;
                    break;
                case KLabel:
                    kind = Kind.KLABEL;
                    break;
                case BagItem:
                    kind = Kind.CELL;
                    break;
                case Bag:
                    kind = Kind.CELL_COLLECTION;
                    break;
                default:
                    assert false: "unexpected lookup kind";
                    kind = null;
            }

            if (lookup instanceof org.kframework.kil.SetLookup) {
                if (lookup.choice()) {
                    lookups.add(new SetElementChoice(base), key);
                } else {
                    lookups.add(new SetLookup(base, key), BoolToken.TRUE);
                }
            } else {
                Term value = (Term) this.visitNode(lookup.value());
                if (lookup instanceof org.kframework.kil.MapLookup) {
                    if (lookup.choice()) {
                        lookups.add(new MapKeyChoice(base), key);
                    }
                    lookups.add(new MapLookup(base, key, kind), value);
                } else { // ListLookup
                    lookups.add(new ListLookup(base, key, kind), value);
                }
            }

        }

        Collection<Variable> freshVariables = new ArrayList<>();
        // TODO(AndreiS): check !Variable only appears in the RHS
        for (org.kframework.kil.Variable variable : node.getBody().variables()) {
            if (variable.isFreshConstant()) {
                freshVariables.add((Variable) this.visitNode(variable));
            }
        }

        assert leftHandSide.kind() == rightHandSide.kind()
               || ((leftHandSide.kind() == Kind.KITEM || leftHandSide.kind() == Kind.K || leftHandSide.kind() == Kind.KLIST)
                   && (rightHandSide.kind() == Kind.KITEM || rightHandSide.kind() == Kind.K || rightHandSide.kind() == Kind.KLIST));

        concreteCollectionSize = Collections.emptyMap();

        java.util.Map<String, Term> lhsOfReadCell = null;
        java.util.Map<String, Term> rhsOfWriteCell = null;
        if (node.isCompiledForFastRewriting()) {
            lhsOfReadCell = Maps.newHashMap();
            for (java.util.Map.Entry<String, org.kframework.kil.Term> entry : node.getLhsOfReadCell().entrySet()) {
                lhsOfReadCell.put(entry.getKey(), (Term) this.visitNode(entry.getValue()));
            }
            rhsOfWriteCell = Maps.newHashMap();
            for (java.util.Map.Entry<String, org.kframework.kil.Term> entry : node.getRhsOfWriteCell().entrySet()) {
                rhsOfWriteCell.put(entry.getKey(), (Term) this.visitNode(entry.getValue()));
            }
        }

        Rule rule = new Rule(
                node.getLabel(),
                leftHandSide,
                rightHandSide,
                requires,
                ensures,
                freshVariables,
                lookups,
                node.isCompiledForFastRewriting(),
                lhsOfReadCell,
                rhsOfWriteCell,
                node.getCellsToCopy(),
                node.getInstructions(),
                node.getAttributes(),
                definition);

        if (freshRules) {
            return rule.getFreshRule(TermContext.of(globalContext));
        }
        return rule;
    }

    private void transformConjunction(Collection<Term> requires, Term term) {
        if (term instanceof KItem &&
               (((KItem) term).kLabel().toString().equals(ANDBOOL_KLABEL.getLabel()) ||
                ((KItem) term).kLabel().toString().equals(BOOL_ANDBOOL_KLABEL.getLabel()))) {
            for (Term item : ((KList) ((KItem) term).kList()).getContents()) {
                requires.add(item);
            }
        } else {
            requires.add(term);
        }
    }

    @Override
    public ASTNode visit(org.kframework.kil.Definition node, Void _) {
        Definition definition = new Definition(context);
        this.definition = definition;
        this.globalContext = new GlobalContext(definition, null);

        Module singletonModule = node.getSingletonModule();

        /*
         * Liyi Li: add new constraint such that if an anywhere rule contains an
         * attribute with "alphaRule" then we remove the rule
         */
        for (org.kframework.kil.Rule rule : singletonModule.getRules()) {
            if (rule.containsAttribute(Attribute.PREDICATE.getKey())
                    || (rule.containsAttribute(Attribute.ANYWHERE.getKey()) && (!rule
                            .containsAttribute("alphaRule")))) {
                continue;
            }

            definition.addRule((Rule) this.visitNode(rule));
        }

        for (String kLabelName : singletonModule.getModuleKLabels()) {
            definition.addKLabel(KLabelConstant.of(kLabelName, definition));
        }

        /* collect the productions which have the attributes strict and seqstrict */
        Set<Production> productions = singletonModule.getSyntaxByTag("strict", context);
        productions.addAll(singletonModule.getSyntaxByTag("seqstrict", context));
        for (Production production : productions) {
            definition.addFrozenKLabel(KLabelConstant.of(production.getKLabel(), definition));
        }

        this.definition = null;
        this.globalContext = null;
        return definition;
    }

    /**
     * Partially evaluate the right-hand side and the conditions for each rule.
     *
     * @param definition
     *            the definition used for evaluation
     * @return the partially evaluated definition
     */
    private static Definition evaluateDefinition(GlobalContext globalContext) {
        Definition definition = globalContext.def;
        /* replace the unevaluated rules defining functions with their partially evaluated counterparts */
        ArrayList<Rule> partiallyEvaluatedRules = new ArrayList<>();
        /* iterate until a fixpoint is reached, because the evaluation with functions uses Term#substituteAndEvalaute */
        while (true) {
            boolean change = false;

            partiallyEvaluatedRules.clear();
            for (Rule rule : definition.functionRules().values()) {
                Rule evaluatedRule = evaluateRule(rule, globalContext);
                partiallyEvaluatedRules.add(evaluatedRule);

                if (!evaluatedRule.equals(rule)) {
                    change = true;
                }
            }

            if (!change) {
                break;
            }

            definition.functionRules().clear();
            definition.addRuleCollection(partiallyEvaluatedRules);
        }

        /* replace the unevaluated rules and macros with their partially evaluated counterparts */
        partiallyEvaluatedRules.clear();
        for (Rule rule : Iterables.concat(definition.rules(), definition.macros())) {
            partiallyEvaluatedRules.add(evaluateRule(rule, globalContext));
        }
        definition.rules().clear();
        definition.macros().clear();
        definition.addRuleCollection(partiallyEvaluatedRules);

        return definition;
    }

    /**
     * Partially evaluate the right-hand side and the conditions of a specified rule.
     * @param rule
     *          the rule being partially evaluated
     * @param definition
     *          the definition used for evaluation
     * @return
     *          the partially evaluated rule
     */
    private static Rule evaluateRule(Rule rule, GlobalContext globalContext) {
        TermContext termContext = TermContext.of(globalContext);
        // TODO(AndreiS): some evaluation is required in the LHS as well
        //Term leftHandSide = rule.leftHandSide().evaluate(termContext);

        Rule origRule = rule;
        if (rule.isFunction()) {
            /*
             * rename variables in the function rule to avoid variable confusion
             * when trying to apply this rule on its RHS
             */
            rule = rule.getFreshRule(termContext);
        }
        Term rightHandSide = rule.rightHandSide().evaluate(termContext);
        List<Term> requires = new ArrayList<>();
        for (Term term : rule.requires()) {
            requires.add(term.evaluate(termContext));
        }
        List<Term> ensures = new ArrayList<>();
        for (Term term : rule.ensures()) {
            ensures.add(term.evaluate(termContext));
        }
        UninterpretedConstraint lookups = new UninterpretedConstraint();
        for (UninterpretedConstraint.Equality equality : rule.lookups().equalities()) {
            lookups.add(
                    equality.leftHandSide().evaluate(termContext),
                    equality.rightHandSide().evaluate(termContext));
        }

        Map<String, Term> rhsOfWriteCell = null;
        if (rule.isCompiledForFastRewriting()) {
            rhsOfWriteCell = new HashMap<>();
            for (Map.Entry<String, Term> entry : rule.rhsOfWriteCell().entrySet()) {
                rhsOfWriteCell.put(entry.getKey(), (Term) entry.getValue().evaluate(termContext));
            }
        }

        Rule newRule = new Rule(
                rule.label(),
                rule.leftHandSide(),
                rightHandSide,
                requires,
                ensures,
                rule.freshVariables(),
                lookups,
                rule.isCompiledForFastRewriting(),
                rule.lhsOfReadCell(),
                rhsOfWriteCell,
                rule.cellsToCopy(),
                rule.instructions(),
                rule.getAttributes(),
                globalContext.def);
        return newRule.equals(rule) ? origRule : newRule;
    }

    private static void flattenKSequence(
            List<org.kframework.kil.Term> flatList,
            List<org.kframework.kil.Term> nestedList) {
        for (org.kframework.kil.Term term : nestedList) {
            if (term instanceof org.kframework.kil.KSequence) {
                org.kframework.kil.KSequence kSequence = (org.kframework.kil.KSequence) term;
                KILtoBackendJavaKILTransformer.flattenKSequence(flatList, kSequence.getContents());
            } else {
                flatList.add(term);
            }
        }
    }

    private static void flattenKList(
            List<org.kframework.kil.Term> flatList,
            List<org.kframework.kil.Term> nestedList) {
        for (org.kframework.kil.Term term : nestedList) {
            if (term instanceof org.kframework.kil.KList) {
                org.kframework.kil.KList kList = (org.kframework.kil.KList) term;
                KILtoBackendJavaKILTransformer.flattenKList(flatList, kList.getContents());
            } else {
                flatList.add(term);
            }
        }
    }
}
