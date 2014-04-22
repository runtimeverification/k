// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.kil.*;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ExperimentalParserOptions;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * A super-visitor class designed to support all use cases for visiting K and KAST syntax.
 * 
 * To use as a visitor, override this class and implement the methods you want to perform
 * an action on. To apply to a term, use {@link ASTNode#accept(Visitor, Object) ASTNode.accept}.
 * 
 * To use this class as a transformer, see {@link AbstractTransformer}.
 * 
 * The algorithm used to implement each of the visitors for each of the different visit methods
 * is as follows:
 * 
 * <ol>
 * <li>Check if we are caching terms and we have seen the term already in the {@link #cache}. 
 * If yes, return the result of visiting that term previously.</li>
 * <li>Check if we are visiting child terms. If not, call the {@code visit} method for the superclass,
 * and return the result. Otherwise, proceed to next step.</li>
 * <li>Visit each child term, and collect the result of calling {@link #processChildTerm(ASTNode, Object)}
 * on each one. If it returns null on the element of a collection or the key or value of a
 * map, delete the entry.</li>
 * <li>Call {@link #changed(ASTNode, ASTNode)} on each child term, and if any are modified, replace
 * them in the tree. If {@link #copy(ASTNode)} returns {@code true} or the node is immutable, 
 * also clone the node itself.</li>
 * <li>Call {@code visit} for the superclass of the term being visited. Once you reach
 * {@link #visit(ASTNode, Object)}, put the result of visiting the object in the cache
 * (if the cache is enabled), and return the result of calling {@link #defaultReturnValue(ASTNode, Object)}
 * on the node.</li>
 * 
 * @author dwightguth
 *
 * @param <P> The parameter to pass to each visit method. Use {@link Void} if not needed, and call
 * {@link ASTNode#accept(Visitor)}.
 * @param <R> The parameter to return from each visit method. Use {@link Void} if not needed, and
 * return {@code null}.
 */
public abstract class AbstractVisitor<P, R, E extends Throwable> implements Visitor<P, R, E> {
    protected org.kframework.kil.loader.Context context;
    protected KompileOptions kompileOptions;
    protected GlobalOptions globalOptions;
    protected ExperimentalParserOptions experimentalParserOptions;
    String name;
    
    protected IdentityHashMap<ASTNode, R> cache = new IdentityHashMap<>();

    public AbstractVisitor(org.kframework.kil.loader.Context context) {
        this.context = context;
        if (context != null) {
            this.kompileOptions = context.kompileOptions;
            this.globalOptions = context.globalOptions;
            this.experimentalParserOptions = context.experimentalParserOptions;
        }
        this.name = this.getClass().toString();
    }

    public AbstractVisitor(String name, org.kframework.kil.loader.Context context) {
        this(context);
        this.name = name;
    }

    @Override
    public R visit(ASTNode node, P p) throws E {
        R ret = defaultReturnValue(node, p);
        return ret;
    }

    @Override
    public R visit(Definition node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<DefinitionItem> items = new ArrayList<>();
            for (DefinitionItem item : node.getItems()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((DefinitionItem) result);
                }
            }
            if (changed(node.getItems(), items)) {
                node = copy(node);
                node.setItems(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(DefinitionItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(LiterateDefinitionComment node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((DefinitionItem) node, p);
    }

    @Override
    public R visit(Module node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<ModuleItem> items = new ArrayList<>();
            for (ModuleItem item : node.getItems()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((ModuleItem) result);
                }
            }
            if (changed(node.getItems(), items)) {
                node = copy(node);
                node.setItems(items);
            }
        }
        return visit((DefinitionItem) node, p);
    }

    @Override
    public R visit(Require node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((DefinitionItem) node, p);
    }

    @Override
    public R visit(ModuleItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Import node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(LiterateModuleComment node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Sentence node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term body = (Term) processChildTerm(node.getBody(), node.getBody().accept(this, p));
            Term requires = node.getRequires();
            if (requires != null)
                requires = (Term) processChildTerm(requires, requires.accept(this, p));
            Term ensures = node.getEnsures();
            if (ensures != null)
                ensures = (Term) processChildTerm(ensures, ensures.accept(this, p));
            if (changed(node.getBody(), body)) {
                node = copy(node);
                node.setBody(body);
            }
            if (changed(node.getRequires(), requires)) {
                node = copy(node);
                node.setRequires(requires);
            }
            if (changed(node.getEnsures(), ensures)) {
                node = copy(node);
                node.setEnsures(ensures);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Configuration node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Sentence) node, p);
    }

    @Override
    public R visit(org.kframework.kil.Context node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Sentence) node, p);
    }

    @Override
    public R visit(Rule node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Sentence) node, p);
    }

    @Override
    public R visit(Syntax node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Sort sort = (Sort)processChildTerm(node.getSort(), node.getSort().accept(this, p));
            List<PriorityBlock> items = new ArrayList<>();
            for (PriorityBlock item : node.getPriorityBlocks()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((PriorityBlock) result);
                }
            }
            if (changed(node.getSort(), sort)) {
                node = copy(node);
                node.setSort(sort);
            }
            if (changed(node.getPriorityBlocks(), items)) {
                node = copy(node);
                node.setPriorityBlocks(items);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(PriorityExtended node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<PriorityBlockExtended> items = new ArrayList<>();
            for (PriorityBlockExtended item : node.getPriorityBlocks()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((PriorityBlockExtended) result);
                }
            }
            if (changed(node.getPriorityBlocks(), items)) {
                node = copy(node);
                node.setPriorityBlocks(items);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(PriorityExtendedAssoc node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<KLabelConstant> items = new ArrayList<>();
            for (KLabelConstant item : node.getTags()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((KLabelConstant) result);
                }
            }
            if (changed(node.getTags(), items)) {
                node = copy(node);
                node.setTags(items);
            }
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(PriorityBlock node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Production> items = new ArrayList<>();
            for (Production item : node.getProductions()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Production) result);
                }
            }
            if (changed(node.getProductions(), items)) {
                node = copy(node);
                node.setProductions(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(PriorityBlockExtended node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<KLabelConstant> items = new ArrayList<>();
            for (KLabelConstant item : node.getProductions()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((KLabelConstant) result);
                }
            }
            if (changed(node.getProductions(), items)) {
                node = copy(node);
                node.setProductions(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Production node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<ProductionItem> items = new ArrayList<>();
            for (ProductionItem item : node.getItems()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((ProductionItem) result);
                }
            }
            if (changed(node.getItems(), items)) {
                node = copy(node);
                node.setItems(items);
            }
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(ProductionItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Sort node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(Terminal node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(Lexical node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(UserList node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ProductionItem) node, p);
    }

    @Override
    public R visit(Term node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(TermComment node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Cell node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node.getContents(), node.getContents().accept(this, p));
            if (changed(node.getContents(), item)) {
                node = copy(node);
                node.setContents(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Collection node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Term> items = new ArrayList<>();
            for (Term item : node.getContents()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Term) result);
                }
            }
            if (changed(node.getContents(), items)) {
                node = copy(node);
                node.setContents(items);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Ambiguity node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(Bag node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(KSequence node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(org.kframework.kil.List node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(KList node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(org.kframework.kil.Map node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(Set node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Collection) node, p);
    }

    @Override
    public R visit(CollectionItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node.getItem(), node.getItem().accept(this, p));
            if (changed(node.getItem(), item)) {
                node = copy(node);
                node.setItem(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(BagItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(ListItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(MapItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node.getKey(), node.getKey().accept(this, p));
            if (changed(node.getKey(), item)) {
                node = copy(node);
                node.setKey(item);
            }
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(SetItem node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionItem) node, p);
    }

    @Override
    public R visit(DataStructureBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            java.util.Collection<Term> items = new ArrayList<>();
            for (Term item : node.baseTerms()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Term) result);
                }
            }
            if (changed(node.baseTerms(), items)) {
                node = node.shallowCopy(items);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(CollectionBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            java.util.Collection<Term> items = new ArrayList<>();
            for (Term item : node.elements()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Term) result);
                }
            }
            if (changed(node.elements(), items)) {
                node = node.shallowCopy(node.baseTerms(), items);
            }
        }
        return visit((DataStructureBuiltin) node, p);
    }

    @Override
    public R visit(SetBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((CollectionBuiltin) node, p);
    }

    @Override
    public R visit(SetLookup node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node.base(), node.base().accept(this, p));
            Term key = (Term) processChildTerm(node.key(), node.key().accept(this, p));
            if (changed(node.base(), base) || changed(node.key(), key)) {
                node = new SetLookup(base, key, node.choice());
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(SetUpdate node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable set = (Variable) processChildTerm(node.set(), node.set().accept(this, p));
            java.util.Collection<Term> items = new ArrayList<>();
            for (Term item : node.removeEntries()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Term) result);
                }
            }
            if (changed(node.set(), set) || changed(node.removeEntries(), items)) {
                node = new SetUpdate(set, items);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(ListBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            java.util.Collection<Term> elementsLeft = new ArrayList<>();
            java.util.Collection<Term> elementsRight = new ArrayList<>();
            for (Term item : node.elementsLeft()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    elementsLeft.add((Term) result);
                }
            }
            for (Term item : node.elementsRight()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    elementsRight.add((Term) result);
                }
            }
            if (changed(node.elementsLeft(), elementsLeft) || changed(node.elementsRight(), elementsRight)) {
                node = ListBuiltin.of(node.sort(), elementsLeft, elementsRight, node.baseTerms());
            }
        }
        return visit((DataStructureBuiltin) node, p);
    }

    @Override
    public R visit(ListLookup node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node.base(), node.base().accept(this, p));
            Term key = (Term) processChildTerm(node.key(), node.key().accept(this, p));
            Term value = (Term) processChildTerm(node.value(), node.value().accept(this, p));
            if (changed(node.base(), base) || changed(node.key(), key)) {
                node = new ListLookup(base, key, value, node.kind());
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(ListUpdate node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node.base(), node.base().accept(this, p));
            java.util.Collection<Term> removeLeft = new ArrayList<>();
            java.util.Collection<Term> removeRight = new ArrayList<>();
            for (Term item : node.removeLeft()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    removeLeft.add((Term) result);
                }
            }
            for (Term item : node.removeRight()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    removeRight.add((Term) result);
                }
            }
            if (changed(node.base(), base) || changed(node.removeLeft(), removeLeft)
                    || changed(node.removeRight(), removeRight)) {
                node = new ListUpdate(base, removeLeft, removeRight);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(MapBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Map<Term, Term> items = new HashMap<>();
            for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
                Term key = (Term) processChildTerm(entry.getKey(), entry.getKey().accept(this, p));
                Term value = (Term) processChildTerm(entry.getValue(), entry.getValue().accept(this, p));
                if (key != null && value != null) {
                    items.put(key, value);
                }
            }
            if (changed(node.elements(), items)) {
                node = new MapBuiltin(node.sort(), node.baseTerms(), items);
            }
        }
        return visit((DataStructureBuiltin) node, p);
    }

    @Override
    public R visit(MapLookup node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable base = (Variable) processChildTerm(node.base(), node.base().accept(this, p));
            Term key = (Term) processChildTerm(node.key(), node.key().accept(this, p));
            Term value = (Term) processChildTerm(node.value(), node.value().accept(this, p));
            if (changed(node.base(), base) || changed(node.key(), key)) {
                node = new MapLookup(base, key, value, node.kind(), node.choice());
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(MapUpdate node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Variable map = (Variable) processChildTerm(node.map(), node.map().accept(this, p));
            Map<Term, Term> removeEntries = new HashMap<>();
            Map<Term, Term> updateEntries = new HashMap<>();
            for (java.util.Map.Entry<Term, Term> entry : node.removeEntries().entrySet()) {
                Term key = (Term) processChildTerm(entry.getKey(), entry.getKey().accept(this, p));
                Term value = (Term) processChildTerm(entry.getValue(), entry.getValue().accept(this, p));
                if (key != null && value != null) {
                    removeEntries.put(key, value);
                }
            }
            for (java.util.Map.Entry<Term, Term> entry : node.updateEntries().entrySet()) {
                Term key = (Term) processChildTerm(entry.getKey(), entry.getKey().accept(this, p));
                Term value = (Term) processChildTerm(entry.getValue(), entry.getValue().accept(this, p));
                if (key != null && value != null) {
                    updateEntries.put(key, value);
                }
            }
            if (changed(node.map(), map) || changed(node.removeEntries(), removeEntries) ||
                    changed(node.updateEntries(), updateEntries)) {
                node = new MapUpdate(map, removeEntries, updateEntries);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Token node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((KLabel) node, p);
    }

    @Override
    public R visit(BoolBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(IntBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(StringBuiltin node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(GenericToken node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Token) node, p);
    }

    @Override
    public R visit(ListTerminator node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Hole node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(FreezerHole node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KApp node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term label = (Term) processChildTerm(node.getLabel(), node.getLabel().accept(this, p));
            Term child = (Term) processChildTerm(node.getChild(), node.getChild().accept(this, p));
            if (changed(node.getLabel(), label)) {
                node = copy(node);
                node.setLabel(label);
            }
            if (changed(node.getChild(), child)) {
                node = copy(node);
                node.setChild(child);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KItemProjection node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node.getTerm(), node.getTerm().accept(this, p));
            if (changed(node.getTerm(), item)) {
                node = copy(node);
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KLabel node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KLabelConstant node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((KLabel) node, p);
    }

    @Override
    public R visit(KLabelInjection node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node.getTerm(), node.getTerm().accept(this, p));
            if (changed(node.getTerm(), item)) {
                node = copy(node);
                node.setTerm(item);
            }
        }
        return visit((KLabel) node, p);
    }

    @Override
    public R visit(Rewrite node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term left = (Term) processChildTerm(node.getLeft(), node.getLeft().accept(this, p));
            Term right = (Term) processChildTerm(node.getRight(), node.getRight().accept(this, p));
            if (changed(node.getLeft(), left)) {
                node = copy(node);
                node.setLeft(left, context);
            }
            if (changed(node.getRight(), right)) {
                node = copy(node);
                node.setRight(right, context);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(TermCons node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Term> items = new ArrayList<>();
            for (Term item : node.getContents()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Term) result);
                }
            }
            if (changed(node.getContents(), items)) {
                node = copy(node);
                node.setContents(items);
            }
        }
        return visit((Term) node, p);
    }
    
    @Override
    public R visit(Attributes node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            List<Attribute> items = new ArrayList<>();
            for (Attribute item : node.getContents()) {
                ASTNode result = processChildTerm(item, item.accept(this, p));
                if (result != null) {
                    items.add((Attribute) result);
                }
            }
            if (changed(node.getContents(), items)) {
                node = copy(node);
                node.setContents(items);
            }
        }
        return visit((ASTNode) node, p);
    }
    

    @Override
    public R visit(Attribute node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }
    
    @Override
    public R visit(ParseError node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ASTNode) node, p);
    }

    @Override
    public R visit(Bracket node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node.getContent(), node.getContent().accept(this, p));
            if (changed(node.getContent(), item)) {
                node = copy(node);
                node.setContent(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Cast node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term)processChildTerm(node.getContent(), node.getContent().accept(this, p));
            if (changed(node.getContent(), item)) {
                node = copy(node);
                node.setContent(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(Variable node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(StringSentence node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Restrictions node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((ModuleItem) node, p);
    }

    @Override
    public R visit(Freezer node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node.getTerm(), node.getTerm().accept(this, p));
            if (changed(node.getTerm(), item)) {
                node = copy(node);
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(BackendTerm node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(KInjectedLabel node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node.getTerm(), node.getTerm().accept(this, p));
            if (changed(node.getTerm(), item)) {
                node = copy(node);
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    @Override
    public R visit(FreezerLabel node, P p) throws E {
        if (cache() && cache.containsKey(node)) {
            return cache.get(node);
        }
        if(visitChildren()) {
            Term item = (Term) processChildTerm(node.getTerm(), node.getTerm().accept(this, p));
            if (changed(node.getTerm(), item)) {
                node = copy(node);
                node.setTerm(item);
            }
        }
        return visit((Term) node, p);
    }

    public String getName() {
        return name;
    }
    
    @Override
    public R complete(ASTNode node, R r) {
        cache.put(node, r);
        return r;
    }
    
    /**
     * Helper method to abstract details of how to decide whether a child term needs to
     * be replaced in the tree.
     * 
     * Right now any object which is not identical to the object that was there before counts as
     * "changed". Theoretically we could inline this method everywhere, but by centralizing it here,
     * that mechanism can be changed later much more easily if we so desire.
     * @param oldObj The child node before potentially being replaced.
     * @param newObj The child node after having potentially been replaced.
     * @return
     */
    public <T extends ASTNode> boolean changed(T oldObj, T newObj) {
        return oldObj != newObj;
    }
    
    /**
     * Helper method to check {@link #changed(ASTNode, ASTNode)} on collections of terms.
     * @param o
     * @param n
     * @return
     */
    public final <T extends ASTNode> boolean changed(java.util.Collection<T> o,
            java.util.Collection<T> n) {
        Iterator<T> iter1 = o.iterator();
        Iterator<T> iter2 = n.iterator();
        boolean change = false;
        while (iter1.hasNext() && iter2.hasNext()) {
            change |= changed(iter1.next(), iter2.next());
        }
        return change || iter1.hasNext() != iter2.hasNext();
    }
    
    /**
     * Helper method to check {@link #changed(ASTNode, ASTNode)} on maps of terms.
     * @param o
     * @param n
     * @return
     */
    public final <K extends ASTNode, V extends ASTNode> boolean changed(
            java.util.Map<K, V> o, java.util.Map<K, V> n) {
        Iterator<Map.Entry<K, V>> iter1 = o.entrySet().iterator();
        Iterator<Map.Entry<K, V>> iter2 = n.entrySet().iterator();
        boolean change = false;
        while (iter1.hasNext() && iter2.hasNext()) {
            Map.Entry<K, V> e1 = iter1.next();
            Map.Entry<K, V> e2 = iter2.next();
            change |= changed(e1.getKey(), e2.getKey());
            change |= changed(e1.getValue(), e2.getValue());
        }
        return change || iter1.hasNext() != iter2.hasNext();
    }
    
    /**
     * The value this transformer returns by default from a {@link #visit(ASTNode, Object)} 
     * or {@link Visitable#accept(Visitor, Object)} invocation if not overriden by the implementation
     * of the visitor. For example, for {@link BasicVisitor}, which returns void, this method returns
     * {@code null}, whereas for {@link AbstractTransformer}, which returns {@link ASTNode}, this
     * method returns {@code node}.
     * @param node The node being visited
     * @param p The optional parameter for the visitor
     * @return The value to return from the visit to this node.
     */
    public abstract R defaultReturnValue(ASTNode node, P p);
    
    /**
     * Determines, based on the information provided from visiting a child term, what term should be
     * reinserted into the tree after the child term is visited. For a visitor which does not transform,
     * this is a no-op, returning {@code node}. For a visitor which transforms its children and
     * replaces them, {@code R} is an {@link ASTNode}, so it returns {@code childResult}.
     * @param child The child term before being visited.
     * @param childResult The result from visiting the child term.
     * @return The term to be reinserted as the new child in the tree.
     */
    public abstract ASTNode processChildTerm(ASTNode child, R childResult);
    
    /**
     * Returns true if this visitor should visit the children of the term being visited, false
     * if only the term itself should be visited.
     * @return
     */
    public abstract boolean visitChildren();
    
    /**
     * Returns true if the result of visiting the tree should be cached by object identity; 
     * false if every term should be visited regardless of sharing.
     * @return
     */
    public abstract boolean cache();
    
    /**
     * Returns the object to pass to the visitor to the parent class of the class being visited. 
     * By combining this field with {@link #defaultReturnValue(ASTNode, Object)}, it is possible
     * to decide whether a visitor should make copies of any terms it modifies. This is used to
     * distinguish {@link BasicTransformer}, which modifies nodes in-place in the tree, and 
     * {@link CopyOnWriteTransformer}, which creates a copy of the tree to return if a node is changed.
     * @param original The node being visited.
     * @return The node as it will be passed to the visit method for its parent class.
     */
    public abstract <T extends ASTNode> T copy(T original);
}
