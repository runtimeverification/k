// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

/** A module. */
public class Module extends DefinitionItem implements Interfaces.MutableList<ModuleItem, Enum<?>> {
    private String name;
    private List<ModuleItem> items = new ArrayList<ModuleItem>();

    public Module(Module m) {
        super(m);
        this.name = m.name;
        this.items = m.items;
    }

    public Module() {
        super();
    }

    public Module(String name) {
        super();
        this.name = name;
    }

    public void appendModuleItem(ModuleItem item) {
        this.items.add(item);
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public void setItems(List<ModuleItem> items) {
        this.items = items;
    }

    public List<ModuleItem> getItems() {
        return items;
    }

    @Override
    public String toString() {
        String content = "";
        for (ModuleItem i : items)
            content += i + " \n";

        return "module " + name + "\n" + content + "\nendmodule";
    }

    public List<String> getModuleKLabels() {
        List<String> mkl = new LinkedList<String>();

        for (ModuleItem mi : items) {
            List<String> list = mi.getKLabels();
            if (list != null)
                mkl.addAll(list);
        }

        return mkl;
    }

    public java.util.Set<String> getAllSorts() {
        java.util.Set<String> sorts = new HashSet<String>();

        for (ModuleItem mi : items) {
            List<String> list = mi.getAllSorts();
            if (list != null)
                sorts.addAll(list);
        }

        // Andrei S: bad, bad practice ...
        // ... but it is 11:55pm and I do not see another way to get them
        sorts.add("#Bool");
        sorts.add("#Int");
        sorts.add("#Float");
        sorts.add("#String");
        sorts.add("#Id");

        return sorts;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    public Module addModuleItems(List<ModuleItem> rules) {
        Module result = new Module(this);
        List<ModuleItem> items = new ArrayList<ModuleItem>(this.items);
        items.addAll(rules);
        result.setItems(items);
        return result;
    }

    @Override
    public Module shallowCopy() {
        return new Module(this);
    }

    public void addSubsort(String sort, String subsort, Context context) {
        this.addProduction(sort, new Sort(subsort));
        context.addSubsort(sort, subsort);
    }

    public void addConstant(String ctSort, String ctName) {
        this.addProduction(ctSort, new Terminal(ctName));
    }

    public void addConstant(KLabelConstant kLabelConstant) {
        this.addProduction(kLabelConstant.getSort(), new Terminal(kLabelConstant.getLabel()));
    }

    public void addProduction(String sort, ProductionItem prodItem) {
        List<ProductionItem> prodItems = new LinkedList<ProductionItem>();
        prodItems.add(prodItem);
        this.addProduction(sort, new Production(new Sort(sort), prodItems));
    }

    public void addProduction(String sort, Production prod) {
        List<PriorityBlock> pbs = new LinkedList<PriorityBlock>();
        PriorityBlock pb = new PriorityBlock();
        pbs.add(pb);

        List<Production> prods = new LinkedList<Production>();
        pb.setProductions(prods);

        prods.add(prod);

        this.items.add(new Syntax(new Sort(sort), pbs));
    }

    public List<Rule> getRules() {
        List<Rule> list = new LinkedList<Rule>();
        for (ModuleItem moduleItem : items) {
            if (moduleItem instanceof Rule) {
                list.add((Rule) moduleItem);
            }
        }

        return list;
    }

    /**
     * Returns a {@code Collection} of {@link Production} instances associated with the given sort.
     */
    public Collection<Production> getProductionsOf(String sort) {
        Collection<Production> productions = new ArrayList<Production>();
        for (ModuleItem item : items) {
            if (!(item instanceof Syntax)) {
                continue;
            }
            Syntax syntax = (Syntax) item;
            if (!syntax.getSort().getName().equals(sort)) {
                continue;
            }
            for (PriorityBlock priorityBlock : syntax.getPriorityBlocks()) {
                productions.addAll(priorityBlock.getProductions());
            }
        }
        return productions;
    }

    @Override
    public List<ModuleItem> getChildren(Enum<?> _) {
        return items;
    }
    
    @Override
    public void setChildren(List<ModuleItem> children, Enum<?> _) {
        this.items = children;
    }

}
