package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CollectionVariable;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.ListLookup;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.SetLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.SetUpdate;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.GenericToken;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.Int32Builtin;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimap;


/**
 * Convert a term from the KIL representation into the Java Rewrite engine internal representation.
 *
 * @author AndreiS
 */
public class KILtoBackendJavaKILTransformer extends CopyOnWriteTransformer {

    private Definition definition = null;
    private Map<org.kframework.kil.Variable, Integer> concreteCollectionSize
            = Collections.emptyMap();

    public KILtoBackendJavaKILTransformer(Context context) {
        super("Transform KIL into java backend KIL", context);
    }

    public Definition transformDefinition(org.kframework.kil.Definition node) {
        try {
            return new MacroExpander((Definition) node.accept(this)).processDefinition();
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }
    }

    public Rule transformRule(org.kframework.kil.Rule node, Definition definition) {
        this.definition = definition;

        Rule rule = null;
        try {
            rule = new MacroExpander(definition).processRule((Rule) node.accept(this));
        } catch (TransformerException e) {
            e.printStackTrace();
        } finally {
            this.definition = null;
        }

        return rule;
    }

    public Term transformTerm(org.kframework.kil.Term node, Definition definition) {
        this.definition = definition;

        Term term = null;
        try {
            term = new MacroExpander(definition).processTerm((Term) node.accept(this));
        } catch (TransformerException e) {
            e.printStackTrace();
        } finally {
            this.definition = null;
        }

        return term;
    }

    @Override
    public ASTNode transform(org.kframework.kil.KApp node) throws TransformerException {
        if (node.getLabel() instanceof org.kframework.kil.Token) {
            if (node.getLabel() instanceof BoolBuiltin) {
                return BoolToken.of(((BoolBuiltin) node.getLabel()).booleanValue());
            } else if (node.getLabel() instanceof IntBuiltin) {
                return IntToken.of(((IntBuiltin) node.getLabel()).bigIntegerValue());
            } else if (node.getLabel() instanceof Int32Builtin) {
                return Int32Token.of(((Int32Builtin) node.getLabel()).intValue());
            } else if (node.getLabel() instanceof StringBuiltin) {
                return StringToken.of(((StringBuiltin) node.getLabel()).stringValue());
            } else if (node.getLabel() instanceof GenericToken) {
                return UninterpretedToken.of(
                        ((GenericToken) node.getLabel()).tokenSort(),
                        ((GenericToken) node.getLabel()).value());
            } else {
                assert false : "unsupported Token " + node.getLabel();
            }
        }

        KLabel kLabel = (KLabel) node.getLabel().accept(this);
        KList kList = (KList) node.getChild().accept(this);

        return new KItem(kLabel, kList, this.context);
    }

    @Override
    public ASTNode transform(org.kframework.kil.KLabelConstant node) throws TransformerException {
        return KLabelConstant.of(node.getLabel(), this.context);
    }

    @Override
    public ASTNode transform(org.kframework.kil.KInjectedLabel node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        return new KLabelInjection(term);
    }

    @Override
    public ASTNode transform(org.kframework.kil.FreezerLabel node) throws TransformerException {
        Term term = (Term) node.getTerm().accept(this);
        return new KLabelFreezer(term);
    }

    @Override
    public ASTNode transform(org.kframework.kil.FreezerHole node) throws TransformerException {
        return Hole.HOLE;
    }

    @Override
    public ASTNode transform(org.kframework.kil.Token node) throws TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode transform(org.kframework.kil.KSequence node) throws TransformerException {
        List<org.kframework.kil.Term> list = new ArrayList<org.kframework.kil.Term>();
        KILtoBackendJavaKILTransformer.flattenKSequence(list, node.getContents());

        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(org.kframework.kil.KSorts.K)) {
            variable = (Variable) list.remove(list.size() - 1).accept(this);
        }

        ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
        for (org.kframework.kil.Term term : list) {
            builder.add((Term) term.accept(this));
        }

        return new KSequence(builder.build(), variable);
    }

    @Override
    public ASTNode transform(org.kframework.kil.KList node) throws TransformerException {
        List<org.kframework.kil.Term> list = new ArrayList<org.kframework.kil.Term>();
        KILtoBackendJavaKILTransformer.flattenKList(list, node.getContents());

        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(org.kframework.kil.KSorts.KLIST)) {
            variable = (Variable) list.remove(list.size() - 1).accept(this);
        }

        ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
        for (org.kframework.kil.Term term : list) {
            builder.add((Term) term.accept(this));
        }

        return new KList(builder.build(), variable);
    }

    @Override
    public ASTNode transform(org.kframework.kil.Cell node) throws TransformerException {
        if (node.getContents() instanceof org.kframework.kil.Bag
                || node.getContents() instanceof org.kframework.kil.Cell) {
            List<org.kframework.kil.Term> contents;
            if (node.getContents() instanceof org.kframework.kil.Bag) {
                contents = new ArrayList<org.kframework.kil.Term>();
                KILtoBackendJavaKILTransformer.flattenBag(
                        contents,
                        ((org.kframework.kil.Bag) node.getContents()).getContents());
            } else {
                contents = Collections.singletonList(node.getContents());
            }

            Multimap<String, Cell> cells = HashMultimap.create();
            Variable variable = null;
            for (org.kframework.kil.Term term : contents) {
                if (term instanceof org.kframework.kil.Cell) {
                    Cell cell = (Cell) term.accept(this);
                    cells.put(cell.getLabel(), cell);
                } else if (variable == null && term instanceof org.kframework.kil.Variable
                        && term.getSort().equals("Bag")) {
                    variable = (Variable) term.accept(this);
                } else {
                    throw new RuntimeException();
                }
            }

            // TODO(AndreiS): get the multiplicity
            boolean isStar = !cells.isEmpty() && cells.keySet().iterator().next().equals("thread");

            return new Cell<CellCollection>(
                    node.getLabel(),
                    new CellCollection(cells, variable, isStar));
        } else {
            Term content = (Term) node.getContents().accept(this);

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
            } else {
                throw new RuntimeException();
            }
        }
    }

    @Override
    public ASTNode transform(org.kframework.kil.ListBuiltin node) throws TransformerException {
        ArrayList<Term> elementsLeft = new ArrayList<Term>(node.elementsLeft().size());
        for (org.kframework.kil.Term entry : node.elementsLeft()) {
            Term newEntry = (Term) entry.accept(this);
            elementsLeft.add(newEntry);
        }

        ArrayList<Term> elementsRight = new ArrayList<Term>(node.elementsRight().size());
        for (org.kframework.kil.Term entry : node.elementsRight()) {
            Term newEntry = (Term) entry.accept(this);
            elementsRight.add(newEntry);
        }

        Term base = null;
        if (node.hasViewBase()) {
            assert node.viewBase() instanceof org.kframework.kil.Variable : "The viewbase " + node.viewBase() +
                    " must be a variable";
            base = (Variable) node.viewBase().accept(this);
        } else {
            Collection<org.kframework.kil.Term> baseTerms = node.baseTerms();
            if (!baseTerms.isEmpty()) {
                assert baseTerms.size() == 1 : "Don't know how to handle multiple base terms for now.";
                org.kframework.kil.Term baseTerm = baseTerms.iterator().next();
                base = (Term) baseTerm.accept(this);
            }
        }
        return BuiltinList.of(base, 0, 0, elementsLeft, elementsRight);
    }

    @Override
    public ASTNode transform(org.kframework.kil.SetBuiltin node) throws TransformerException {
        assert node.isLHSView() : "unsupported set " + node;

        HashSet<Term> entries = new HashSet<Term>(node.elements().size());
        for (org.kframework.kil.Term entry : node.elements()) {
            Term key = (Term) entry.accept(this);
            entries.add(key);
        }

        if (node.hasViewBase()) {
            Term base = (Term) node.viewBase().accept(this);
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
    }

    @Override
    public ASTNode transform(org.kframework.kil.MapBuiltin node) throws TransformerException {
        assert node.isLHSView() : "unsupported map " + node;

        HashMap<Term, Term> entries = new HashMap<Term, Term>(node.elements().size());
        for (Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.elements().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);
            entries.put(key, value);
        }

        if (node.hasViewBase()) {
            Term base = (Term) node.viewBase().accept(this);
            if (base instanceof MapUpdate) {
                MapUpdate mapUpdate = (MapUpdate) base;
                /* TODO(AndreiS): check key uniqueness */
                entries.putAll(mapUpdate.updateMap());
                return new MapUpdate(mapUpdate.map(), mapUpdate.removeSet(), entries);
            } else {
                /* base instanceof Variable */
                return new BuiltinMap(entries, (Variable) base);
            }
        } else {
            return new BuiltinMap(entries);
        }
    }

    @Override
    public ASTNode transform(org.kframework.kil.ListUpdate node) throws TransformerException {
        Variable base = (Variable) node.base().accept(this);

        return BuiltinList.of(base, node.removeLeft().size(), node.removeRight().size(),
                Collections.<Term>emptyList(), Collections.<Term>emptyList());
    }

    @Override
    public ASTNode transform(org.kframework.kil.SetUpdate node) throws TransformerException {
        Variable set = (Variable) node.set().accept(this);

        HashSet<Term> removeSet = new HashSet<Term>(node.removeEntries().size());
        for (org.kframework.kil.Term term : node.removeEntries()) {
            removeSet.add((Term) term.accept(this));
        }

        return new SetUpdate(set, removeSet);
    }

     @Override
    public ASTNode transform(org.kframework.kil.MapUpdate node) throws TransformerException {
        Variable map = (Variable) node.map().accept(this);

        HashSet<Term> removeSet = new HashSet<Term>(node.removeEntries().size());
        for (org.kframework.kil.Term term : node.removeEntries().keySet()) {
            removeSet.add((Term) term.accept(this));
        }

        HashMap<Term, Term> updateMap = new HashMap<Term, Term>(node.updateEntries().size());
        for (Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.updateEntries().entrySet()) {
            Term key = (Term) entry.getKey().accept(this);
            Term value = (Term) entry.getValue().accept(this);
            updateMap.put(key, value);
        }

        return new MapUpdate(map, removeSet, updateMap);
    }

    @Override
    public ASTNode transform(org.kframework.kil.Variable node) throws TransformerException {
        if (node.getSort().equals("Bag")) {
            return new Variable(node.getName(), Kind.CELL_COLLECTION.toString());
        }

        DataStructureSort dataStructureSort = context.dataStructureSortOf(node.getSort());
        if (dataStructureSort != null) {
            String sort = null;
            if (dataStructureSort.type().equals(org.kframework.kil.KSorts.LIST)) {
                sort = KSorts.LIST;
            } else if (dataStructureSort.type().equals(org.kframework.kil.KSorts.MAP)) {
                sort = KSorts.MAP;
            } else if (dataStructureSort.type().equals(org.kframework.kil.KSorts.SET)) {
                sort = KSorts.SET;
            } else {
                assert false: "unexpected data structure " + dataStructureSort.type();
            }

            if (concreteCollectionSize.containsKey(node)) {
                return new CollectionVariable(
                        node.getName(),
                        sort,
                        concreteCollectionSize.get(node));
            } else {
                return new Variable(node.getName(), sort);
            }
        }
        return new Variable(node.getName(), node.getSort());
    }

    @Override
    public ASTNode transform(org.kframework.kil.Rule node) throws TransformerException {
        assert node.getBody() instanceof org.kframework.kil.Rewrite;

        concreteCollectionSize = node.getConcreteDataStructureSize();

        org.kframework.kil.Rewrite rewrite = (org.kframework.kil.Rewrite) node.getBody();
        Term leftHandSide = (Term) rewrite.getLeft().accept(this);
        Term rightHandSide = (Term) rewrite.getRight().accept(this);

        Collection<Term> requires = new ArrayList<Term>();
        Collection<Variable> freshVariables = new ArrayList<Variable>();
        //TODO: Deal with Ensures
        if (node.getRequires() != null) {
            Term term = (Term) node.getRequires().accept(this);
            if (term instanceof KItem && ((KItem) term).kLabel().toString().equals("'_andBool_")) {
                for (Term item : ((KItem) term).kList().getItems()) {
                    if (item instanceof KItem && ((KItem) item).kLabel().toString().equals("'fresh(_)")) {
                        freshVariables.add((Variable) ((KItem) item).kList().get(0));
                    } else {
                        requires.add(item);
                    }
                }
            } else {
                if (term instanceof KItem && ((KItem) term).kLabel().toString().equals("'fresh(_)")) {
                    freshVariables.add((Variable) ((KItem) term).kList().get(0));
                } else {
                    requires.add(term);
                }
            }
        }

        UninterpretedConstraint lookups = new UninterpretedConstraint();
        for (org.kframework.kil.BuiltinLookup lookup : node.getLookups()) {
            Variable base = (Variable) lookup.base().accept(this);
            Term key = (Term) lookup.key().accept(this);

            if (lookup instanceof org.kframework.kil.SetLookup) {
                lookups.add(new SetLookup(base, key), BoolToken.TRUE);
            } else {
                Term value = (Term) lookup.value().accept(this);
                if (lookup instanceof org.kframework.kil.MapLookup) {
                    lookups.add(new MapLookup(base, key), value);
                } else { // ListLookup
                    lookups.add(new ListLookup(base, key), value);
                }
            }

        }

        assert leftHandSide.kind() == rightHandSide.kind()
               || ((leftHandSide.kind() == Kind.KITEM || leftHandSide.kind() == Kind.K || leftHandSide.kind() == Kind.KLIST)
                   && (rightHandSide.kind() == Kind.KITEM || rightHandSide.kind() == Kind.K || rightHandSide.kind() == Kind.KLIST));

        concreteCollectionSize = Collections.emptyMap();

        Rule rule = new Rule(
                leftHandSide,
                rightHandSide,
                requires,
                freshVariables,
                lookups,
                node.getAttributes());

        return rule.getFreshRule(new TermContext(definition));
    }

    @Override
    public ASTNode transform(org.kframework.kil.Definition node) {
        Definition definition = new Definition(context);
        this.definition = definition;

        Module singletonModule = node.getSingletonModule();

        for (org.kframework.kil.Rule rule : singletonModule.getRules()) {
            if (!rule.containsAttribute(SymbolicBackend.SYMBOLIC)
                || rule.containsAttribute(Attribute.PREDICATE.getKey())
                || rule.containsAttribute(Attribute.ANYWHERE.getKey())) {
                continue;
            }

            try {
                definition.addRule((Rule) rule.accept(this));
            } catch (TransformerException e) {
                System.err.println(rule);
                System.err.flush();
                e.printStackTrace();
            }
        }

        for (String kLabelName : singletonModule.getModuleKLabels()) {
            definition.addKLabel(KLabelConstant.of(kLabelName, context));
        }

        /* collect the productions which have the attributes strict and seqstrict */
        Set<Production> productions = singletonModule.getSyntaxByTag("strict", context);
        productions.addAll(singletonModule.getSyntaxByTag("seqstrict", context));
        for (Production production : productions) {
            definition.addFrozenKLabel(KLabelConstant.of(production.getKLabel(), context));
        }

        this.definition = null;
        return definition;
    }

    private static void flattenBag(
            List<org.kframework.kil.Term> flatBag,
            List<org.kframework.kil.Term> nestedBag) {
        for (org.kframework.kil.Term term : nestedBag) {
            if (term instanceof org.kframework.kil.Bag) {
                org.kframework.kil.Bag bag = (org.kframework.kil.Bag) term;
                KILtoBackendJavaKILTransformer.flattenBag(flatBag, bag.getContents());
            } else {
                flatBag.add(term);
            }
        }
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
