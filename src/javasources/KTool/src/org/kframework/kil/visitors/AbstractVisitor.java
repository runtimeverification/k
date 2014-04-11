package org.kframework.kil.visitors;

import org.kframework.kil.*;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ExperimentalParserOptions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

//TODO(dwightguth): 
/**
 * A super-visitor class designed to support all use cases for visiting K and KAST syntax.
 * 
 * To use as a visitor, override this class and implement the methods you want to perform
 * an action on. To apply to a term, use {@link ASTNode#accept(Visitor, Object) ASTNode.accept}.
 * 
 * To use this class as a transformer, see {@link BasicTransformer}.
 * @author dwightguth
 *
 * @param <P> The parameter to pass to each visit method. Use {@link Void} if not needed, and call
 * {@link ASTNode#accept(Visitor)}.
 * @param <R> The parameter to return from each visit method. Use {@link Void} if not needed, and
 * return {@code null}.
 */
public abstract class AbstractVisitor<P, R> implements Visitor<P, R> {
    protected org.kframework.kil.loader.Context context;
    protected KompileOptions kompileOptions;
    protected GlobalOptions globalOptions;
    protected ExperimentalParserOptions experimentalParserOptions;
    String name;
    
    protected java.util.Map<ASTNode, R> cache = new HashMap<>();

    public AbstractVisitor(org.kframework.kil.loader.Context context) {
        this.context = context;
        this.kompileOptions = context.kompileOptions;
        this.globalOptions = context.globalOptions;
        this.experimentalParserOptions = context.experimentalParserOptions;
    }

    public AbstractVisitor(String name, org.kframework.kil.loader.Context context) {
        this(context);
        this.name = name;
    }

    @Override
    public R visit(ASTNode node, P p) {
        R ret = defaultReturnValue(node, p);
        cache.put(node, ret);
        return ret;
    }

    @Override
    public R visit(Definition node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<DefinitionItem> items = new ArrayList<>();
            for (DefinitionItem item : node.getItems()) {
                items.add((DefinitionItem)processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getItems(), items)) {
                node.setItems(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(DefinitionItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(LiterateDefinitionComment node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((DefinitionItem) node, p);
    }

    @Override
    public R visit(Module node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<ModuleItem> items = new ArrayList<>();
            for (ModuleItem item : node.getItems()) {
                items.add((ModuleItem)processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getItems(), items)) {
                node.setItems(items);
            }
        }
        return visit((DefinitionItem) node, p);
    }

    @Override
    public R visit(Require node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((DefinitionItem) node, p);
    }

    @Override
    public R visit(ModuleItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Import node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(LiterateModuleComment node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Sentence node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term body = (Term) processChildTerm(node, node.getBody(), node.getBody().accept(this, p), p);
            Term requires = node.getRequires();
            if (requires != null)
                requires = (Term) processChildTerm(node, requires, requires.accept(this, p), p);
            Term ensures = node.getEnsures();
            if (ensures != null)
                ensures = (Term) processChildTerm(node, ensures, ensures.accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getBody(), body)) {
                node.setBody(body);
            }
            if (change(node.getRequires(), requires)) {
                node.setRequires(requires);
            }
            if (change(node.getEnsures(), ensures)) {
                node.setEnsures(ensures);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Configuration node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Sentence) node, p);
    }

    @Override
    public R visit(org.kframework.kil.Context node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Sentence) node, p);
    }

    @Override
    public R visit(Rule node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Sentence) node, p);
    }

    @Override
    public R visit(Syntax node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Sort sort = (Sort)processChildTerm(node, node.getSort(), node.getSort().accept(this, p), p);
            List<PriorityBlock> items = new ArrayList<>();
            for (PriorityBlock item : node.getPriorityBlocks()) {
                items.add((PriorityBlock) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getSort(), sort)) {
                node.setSort(sort);
            }
            if (change(node.getPriorityBlocks(), items)) {
                node.setPriorityBlocks(items);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(PriorityExtended node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<PriorityBlockExtended> items = new ArrayList<>();
            for (PriorityBlockExtended item : node.getPriorityBlocks()) {
                items.add((PriorityBlockExtended) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getPriorityBlocks(), items)) {
                node.setPriorityBlocks(items);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(PriorityExtendedAssoc node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<KLabelConstant> items = new ArrayList<>();
            for (KLabelConstant item : node.getTags()) {
                    items.add((KLabelConstant) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getTags(), items)) {
                node.setTags(items);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(PriorityBlock node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Production> items = new ArrayList<>();
            for (Production item : node.getProductions()) {
                items.add((Production) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getProductions(), items)) {
                node.setProductions(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(PriorityBlockExtended node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<KLabelConstant> items = new ArrayList<>();
            for (KLabelConstant item : node.getProductions()) {
                items.add((KLabelConstant) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getProductions(), items)) {
                node.setProductions(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Production node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<ProductionItem> items = new ArrayList<>();
            for (ProductionItem item : node.getItems()) {
                items.add((ProductionItem) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getItems(), items)) {
                node.setItems(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(ProductionItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Sort node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(Terminal node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(Lexical node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(UserList node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(Term node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(TermComment node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Cell node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node, node.getContents(), node.getContents().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getContents(), item)) {
                node.setContents(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Collection node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Term> items = new ArrayList<>();
            for (int i = 0; i < node.getContents().size(); i++) {
                items.add((Term) processChildTerm(node, node.getContents().get(i), node.getContents().get(i).accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getContents(), items)) {
                node.setContents(items);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Ambiguity node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(Bag node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(KSequence node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(org.kframework.kil.List node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(KList node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(org.kframework.kil.Map node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(Set node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(CollectionItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node, node.getItem(), node.getItem().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getItem(), item)) {
                node.setItem(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(BagItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(ListItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(MapItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(SetItem node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(DataStructureBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            java.util.Collection<Term> items = new ArrayList<>();
            for (Term item : node.baseTerms()) {
                items.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (change(node.baseTerms(), items)) {
                node = DataStructureBuiltin.of(node.sort(), items.toArray(new Term[items.size()]));
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(CollectionBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            java.util.Collection<Term> items = new ArrayList<>();
            for (Term item : node.elements()) {
                items.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (change(node.elements(), items)) {
                node = CollectionBuiltin.of(node.sort(), node.baseTerms(), items);
            }
        }
        return visit((DataStructureBuiltin) node, p);
    }

    @Override
    public R visit(SetBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionBuiltin) node, p);
    }

    @Override
    public R visit(SetLookup node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node, node.base(), node.base().accept(this, p), p);
            Term key = (Term) processChildTerm(node, node.key(), node.key().accept(this, p), p);
            if (change(node.base(), base) || change(node.key(), key)) {
                node = new SetLookup(base, key, node.choice());
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(SetUpdate node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable set = (Variable) processChildTerm(node, node.set(), node.set().accept(this, p), p);
            java.util.Collection<Term> items = new ArrayList<>();
            for (Term item : node.removeEntries()) {
                items.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (change(node.set(), set) || change(node.removeEntries(), items)) {
                node = new SetUpdate(set, items);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(ListBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            java.util.Collection<Term> elementsLeft = new ArrayList<>();
            java.util.Collection<Term> elementsRight = new ArrayList<>();
            for (Term item : node.elementsLeft()) {
                elementsLeft.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            for (Term item : node.elementsRight()) {
                elementsRight.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (change(node.elementsLeft(), elementsLeft) || change(node.elementsRight(), elementsRight)) {
                node = ListBuiltin.of(node.sort(), elementsLeft, elementsRight, node.baseTerms());
            }
        }
        return visit((DataStructureBuiltin) node, p);
    }

    @Override
    public R visit(ListLookup node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node, node.base(), node.base().accept(this, p), p);
            Term key = (Term) processChildTerm(node, node.key(), node.key().accept(this, p), p);
            Term value = (Term) processChildTerm(node, node.value(), node.value().accept(this, p), p);
            if (change(node.base(), base) || change(node.key(), key)) {
                node = new ListLookup(base, key, value, node.kind());
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(ListUpdate node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node, node.base(), node.base().accept(this, p), p);
            java.util.Collection<Term> removeLeft = new ArrayList<>();
            java.util.Collection<Term> removeRight = new ArrayList<>();
            for (Term item : node.removeLeft()) {
                removeLeft.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            for (Term item : node.removeRight()) {
                removeRight.add((Term) processChildTerm(node, item, item.accept(this, p), p));
            }
            if (change(node.base(), base) || change(node.removeLeft(), removeLeft)
                    || change(node.removeRight(), removeRight)) {
                node = new ListUpdate(base, removeLeft, removeRight);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(MapBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Map<Term, Term> items = new HashMap<>();
            for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
                Term key = (Term) processChildTerm(node, entry.getKey(), entry.getKey().accept(this, p), p);
                Term value = (Term) processChildTerm(node, entry.getValue(), entry.getValue().accept(this, p), p);
                items.put(key, value);
            }
            if (change(node.elements(), items)) {
                node = new MapBuiltin(node.sort(), node.baseTerms(), items);
            }
        }
        return visit((DataStructureBuiltin) node, p);
    }

    @Override
    public R visit(MapLookup node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node, node.base(), node.base().accept(this, p), p);
            Term key = (Term) processChildTerm(node, node.key(), node.key().accept(this, p), p);
            Term value = (Term) processChildTerm(node, node.value(), node.value().accept(this, p), p);
            if (change(node.base(), base) || change(node.key(), key)) {
                node = new MapLookup(base, key, value, node.kind(), node.choice());
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(MapUpdate node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable map = (Variable) processChildTerm(node, node.map(), node.map().accept(this, p), p);
            Map<Term, Term> removeEntries = new HashMap<>();
            Map<Term, Term> updateEntries = new HashMap<>();
            for (java.util.Map.Entry<Term, Term> entry : node.removeEntries().entrySet()) {
                Term key = (Term) processChildTerm(node, entry.getKey(), entry.getKey().accept(this, p), p);
                Term value = (Term) processChildTerm(node, entry.getValue(), entry.getValue().accept(this, p), p);
                removeEntries.put(key, value);
            }
            for (java.util.Map.Entry<Term, Term> entry : node.updateEntries().entrySet()) {
                Term key = (Term) processChildTerm(node, entry.getKey(), entry.getKey().accept(this, p), p);
                Term value = (Term) processChildTerm(node, entry.getValue(), entry.getValue().accept(this, p), p);
                updateEntries.put(key, value);
            }
            if (change(node.map(), map) || change(node.removeEntries(), removeEntries) ||
                    change(node.updateEntries(), updateEntries)) {
                node = new MapUpdate(map, removeEntries, updateEntries);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Token node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((KLabel) node, p);
    }

    @Override
    public R visit(BoolBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(IntBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(StringBuiltin node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(GenericToken node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(ListTerminator node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Hole node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(FreezerHole node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KApp node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term label = (Term) processChildTerm(node, node.getLabel(), node.getLabel().accept(this, p), p);
            Term child = (Term) processChildTerm(node, node.getChild(), node.getChild().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getLabel(), label)) {
                node.setLabel(label);
            }
            if (change(node.getChild(), child)) {
                node.setChild(child);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KItemProjection node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node, node.getTerm(), node.getTerm().accept(this, p), p);
            if (copy()) {
                 node = node.shallowCopy();
            }
            if (change(node.getTerm(), item)) {
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KLabel node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KLabelConstant node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((KLabel) node, p);
    }

    @Override
    public R visit(KLabelInjection node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node, node.getTerm(), node.getTerm().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getTerm(), item)) {
                node.setTerm(item);
            }
        }
        return visit((KLabel) node, p);
    }

    @Override
    public R visit(Rewrite node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term left = (Term) processChildTerm(node, node.getLeft(), node.getLeft().accept(this, p), p);
            Term right = (Term) processChildTerm(node, node.getRight(), node.getRight().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getLeft(), left)) {
                node.setLeft(left, context);
            }
            if (change(node.getRight(), right)) {
                node.setRight(right, context);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(TermCons node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Term> items = new ArrayList<>();
            for (int i = 0; i < node.getContents().size(); i++) {
                items.add((Term) processChildTerm(node, node.getContents().get(i), node.getContents().get(i).accept(this, p), p));
            }
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getContents(), items)) {
                node.setContents(items);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Bracket node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node, node.getContent(), node.getContent().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getContent(), item)) {
                node.setContent(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Cast node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node, node.getContent(), node.getContent().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getContent(), item)) {
                node.setContent(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Variable node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(StringSentence node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Restrictions node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Freezer node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node, node.getTerm(), node.getTerm().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getTerm(), item)) {
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(BackendTerm node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KInjectedLabel node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node, node.getTerm(), node.getTerm().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getTerm(), item)) {
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(FreezerLabel node, P p) {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node, node.getTerm(), node.getTerm().accept(this, p), p);
            if (copy()) {
                node = node.shallowCopy();
            }
            if (change(node.getTerm(), item)) {
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    public String getName() {
        return name;
    }
    
    public final <T extends ASTNode> boolean change(java.util.Collection<T> o,
            java.util.Collection<T> n) {
        Iterator<T> iter1 = o.iterator();
        Iterator<T> iter2 = n.iterator();
        boolean change = false;
        while (iter1.hasNext() && iter2.hasNext()) {
            change |= change(iter1.next(), iter2.next());
        }
        return change || iter1.hasNext() != iter2.hasNext();
    }
    
    public final <K extends ASTNode, V extends ASTNode> boolean change(
            java.util.Map<K, V> o, java.util.Map<K, V> n) {
        Iterator<Map.Entry<K, V>> iter1 = o.entrySet().iterator();
        Iterator<Map.Entry<K, V>> iter2 = n.entrySet().iterator();
        boolean change = false;
        while (iter1.hasNext() && iter2.hasNext()) {
            Map.Entry<K, V> e1 = iter1.next();
            Map.Entry<K, V> e2 = iter2.next();
            change |= change(e1.getKey(), e2.getKey());
            change |= change(e1.getValue(), e2.getValue());
        }
        return change || iter1.hasNext() != iter2.hasNext();
    }
    
    public abstract R defaultReturnValue(ASTNode node, P p);
    public abstract ASTNode processChildTerm(ASTNode node, ASTNode child, R childResult, P p);
    public abstract boolean visitChildren();
    public abstract boolean cache();
    public abstract boolean copy();
    public abstract <T extends ASTNode> boolean change(T o, T n);
}