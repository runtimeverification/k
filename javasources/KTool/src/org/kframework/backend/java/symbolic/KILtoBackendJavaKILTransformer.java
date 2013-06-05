package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.kil.BoolToken;
import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.IntToken;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.UninterpretedToken;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.GenericToken;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KSorts;
import org.kframework.kil.Token;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;


/**
 * Convert
 *
 * @author AndreiS
 */
public class KILtoBackendJavaKILTransformer extends CopyOnWriteTransformer {

    public KILtoBackendJavaKILTransformer(Context context) {
        super("Transform KIL into java backend KIL", context);
    }

    @Override
    public ASTNode transform(org.kframework.kil.KApp node) throws TransformerException {
        if (node.getLabel() instanceof Token) {
            if (node.getLabel() instanceof BoolBuiltin) {
                return BoolToken.of(((BoolBuiltin) node.getLabel()).booleanValue());
            } else if (node.getLabel() instanceof IntBuiltin) {
                return IntToken.of(((IntBuiltin) node.getLabel()).bigIntegerValue());
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
        return new BuiltinConstant(node.value(), node.tokenSort());
    }

    @Override
    public ASTNode transform(org.kframework.kil.KSequence node) throws TransformerException {
        List<org.kframework.kil.Term> list = node.getContents();
        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(KSorts.K)) {
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
        List<org.kframework.kil.Term> list = node.getContents();
        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(KSorts.KLIST)) {
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
        if (node.getContents() instanceof org.kframework.kil.Bag) {
            org.kframework.kil.Bag bag = (org.kframework.kil.Bag) node.getContents();

            java.util.Map<String, Cell> cells = new HashMap<String, Cell>();
            Variable variable = null;
            for (org.kframework.kil.Term term : bag.getContents()) {
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

            return new Cell<CellCollection>(node.getLabel(), new CellCollection(cells, variable));
        } else {
            Term content = (Term) node.getContents().accept(this);
            if (content instanceof KItem) {
                return new Cell<KItem>(node.getLabel(), (KItem) content);
            } else if (content instanceof KSequence) {
                return new Cell<KSequence>(node.getLabel(), (KSequence) content);
            } else if (content instanceof KList) {
                return new Cell<KList>(node.getLabel(), (KList) content);
            } else if (content instanceof Map) {
                return new Cell<Map>(node.getLabel(), (Map) content);
            } else if (content instanceof Variable) {
                return new Cell<Term>(node.getLabel(), content);
            } else {
                throw new RuntimeException();
            }
        }
    }

    @Override
    public ASTNode transform(org.kframework.kil.MapBuiltin node) throws TransformerException {
        assert node.isLHSView() : "unsupported map " + node;

        HashMap<Term, Term> entries = new HashMap<Term, Term>(node.elements().size());
        for (java.util.Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
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
                return new Map(entries, (Variable) base);
            }
        } else {
            return new Map(entries);
        }
    }

    @Override
    public ASTNode transform(org.kframework.kil.MapUpdate node) throws TransformerException {
        Variable map = (Variable) node.map().accept(this);

        HashSet<Term> removeSet = new HashSet<Term>(node.removeSet().size());
        for (org.kframework.kil.Term term : node.removeSet()) {
            removeSet.add((Term) term.accept(this));
        }

        HashMap<Term, Term> updateMap = new HashMap<Term, Term>(node.updateMap().size());
        for (java.util.Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.updateMap().entrySet()) {
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
        } else if (context.dataStructureSortOf(node.getSort()) != null
                && context.dataStructureSortOf(node.getSort()).type().equals(KSorts.MAP)) {
            return new Variable(node.getName(), Kind.MAP.toString());
        } else {
            return new Variable(node.getName(), node.getSort());
        }
    }

    @Override
    public ASTNode transform(org.kframework.kil.Rule node) throws TransformerException {
        assert node.getBody() instanceof org.kframework.kil.Rewrite;

        org.kframework.kil.Rewrite rewrite = (org.kframework.kil.Rewrite) node.getBody();
        Term leftHandSide = (Term) rewrite.getLeft().accept(this);
        //System.err.println(leftHandSide);
        //System.err.flush();
        Term rightHandSide = (Term) rewrite.getRight().accept(this);
        //System.err.println(rightHandSide);
        //System.err.flush();
        Term condition = null;
        if (node.getCondition() != null) {
            System.err.println("[error]: " + node.getCondition());
            System.err.flush();
            // TODO(AndreiS): handle conditions
            condition = (Term) node.getCondition().accept(this);
        }

        List<Term> values = new ArrayList<Term>();
        List<MapLookup> lookups = new ArrayList<MapLookup>();
        for (org.kframework.kil.MapLookup lookup : node.getLookups()) {
            Variable map = (Variable) lookup.map().accept(this);
            Term key = (Term) lookup.key().accept(this);
            lookups.add(new MapLookup(map, key));
            Term value = (Term) lookup.value().accept(this);
            values.add(value);
        }

        assert leftHandSide.getKind().equals(rightHandSide.getKind());

        return new Rule(
                leftHandSide,
                rightHandSide,
                condition,
                lookups,
                values,
                node.getAttributes());
    }

    @Override
    public ASTNode transform(org.kframework.kil.Definition definition) {
        List<Rule> rules = new ArrayList<Rule>(definition.getSingletonModule().getRules().size());
        for (org.kframework.kil.Rule rule : definition.getSingletonModule().getRules()) {
            if (!rule.containsAttribute(SymbolicBackend.SYMBOLIC)
                || rule.containsAttribute(Attribute.FUNCTION.getKey())
                || rule.containsAttribute(Attribute.PREDICATE.getKey())
                || rule.containsAttribute(Attribute.ANYWHERE.getKey())) {
                continue;
            }

            try {
                //System.err.println(rule);
                //System.err.flush();
                rules.add((Rule) rule.accept(this));
            } catch (TransformerException e) {
                System.err.println(rule);
                System.err.flush();
                e.printStackTrace();
            }
        }
        return new Definition(rules);
    }

}
