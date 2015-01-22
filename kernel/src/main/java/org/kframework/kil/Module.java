// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.ModuleContext;
import org.kframework.kil.visitors.Visitor;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.parser.concrete2.KSyntax2GrammarStatesFilter;
import org.kframework.parser.generator.CollectTerminalsVisitor;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

/** A module. */
public class Module extends DefinitionItem implements Interfaces.MutableList<ModuleItem, Enum<?>> {
    private String name;
    private List<ModuleItem> items = new ArrayList<>();

    // keeps easy to access information about the current module
    private transient ModuleContext moduleContext = new ModuleContext();

    // lazily computed set of sorts.
    private Set<Sort> sorts;

    public Module(Module m) {
        super(m);
        this.name = m.name;
        this.items = m.items;
        this.sorts = m.sorts;
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
        this.sorts = null;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public void setItems(List<ModuleItem> items) {
        this.items = items;
        this.sorts = null;
    }

    public List<ModuleItem> getItems() {
        return items;
    }

    @Override
    public String toString() {
        String content = "";
        List<ModuleItem> sortedItems = new ArrayList<ModuleItem>(items);

        sortedItems.sort(new Comparator<ModuleItem>() {
            @Override
            public int compare(ModuleItem o1, ModuleItem o2) {
                return o1.toString().compareTo(o2.toString());
            }
        });

        for (ModuleItem i : sortedItems)
            content += i + " \n";

        return "module " + name + "\n" + content + "\nendmodule";
    }

    public List<String> getModuleKLabels() {
        List<String> mkl = new LinkedList<>();

        for (ModuleItem mi : items) {
            List<String> list = mi.getKLabels();
            if (list != null)
                mkl.addAll(list);
        }

        return mkl;
    }

    /**
     * Return a list of the sorts declared by
     * items in this module, plus a few builtin
     * sorts.
     * Result will contain duplicates if
     * multiple declarations mention the same sort.
     * @return
     */
    public Set<Sort> getAllSorts() {
        if (sorts != null) {
            return sorts;
        }
        sorts = new LinkedHashSet<>();
        for (ModuleItem mi : items) {
            List<Sort> list = mi.getAllSorts();
            if (list != null)
                sorts.addAll(list);
        }

        sorts.add(Sort.BUILTIN_BOOL);
        sorts.add(Sort.BUILTIN_INT);
        sorts.add(Sort.BUILTIN_FLOAT);
        sorts.add(Sort.BUILTIN_STRING);
        sorts.add(Sort.BUILTIN_ID);

        return sorts;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    public Module addModuleItems(List<ModuleItem> rules) {
        Module result = new Module(this);
        List<ModuleItem> items = new ArrayList<>(this.items);
        items.addAll(rules);
        this.sorts = null;
        result.setItems(items);
        return result;
    }

    @Override
    public Module shallowCopy() {
        return new Module(this);
    }

    public void addSubsort(Sort sort, Sort subsort, Context context) {
        this.addProduction(sort, new NonTerminal(subsort));
        context.addSubsort(sort, subsort);
    }

    public void addConstant(Sort ctSort, String ctName) {
        this.addProduction(ctSort, new Terminal(ctName));
    }

    public void addConstant(KLabelConstant kLabelConstant) {
        this.addProduction(kLabelConstant.getSort(), new Terminal(kLabelConstant.getLabel()));
    }

    public void addProduction(Sort sort, ProductionItem prodItem) {
        List<ProductionItem> prodItems = new LinkedList<>();
        prodItems.add(prodItem);
        this.addProduction(sort, new Production(new NonTerminal(sort), prodItems));
    }

    public void addProduction(Sort sort, Production prod) {
        List<PriorityBlock> pbs = new LinkedList<>();
        PriorityBlock pb = new PriorityBlock();
        pbs.add(pb);

        List<Production> prods = new LinkedList<>();
        pb.setProductions(prods);

        prods.add(prod);

        this.items.add(new Syntax(new NonTerminal(sort), pbs));
        this.sorts = null;
    }

    public List<Rule> getRules() {
        List<Rule> list = new LinkedList<>();
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
    public Collection<Production> getProductionsOf(Sort sort) {
        Collection<Production> productions = new ArrayList<>();
        for (ModuleItem item : items) {
            if (!(item instanceof Syntax)) {
                continue;
            }
            Syntax syntax = (Syntax) item;
            if (!syntax.getDeclaredSort().getSort().equals(sort)) {
                continue;
            }
            for (PriorityBlock priorityBlock : syntax.getPriorityBlocks()) {
                productions.addAll(priorityBlock.getProductions());
            }
        }
        return productions;
    }

    @Override
    public List<ModuleItem> getChildren(Enum<?> _void) {
        return items;
    }

    @Override
    public void setChildren(List<ModuleItem> children, Enum<?> _void) {
        this.items = children;
        this.sorts = null;
    }

    public ModuleContext getModuleContext() {
        return moduleContext;
    }

    public Grammar getRuleGrammar(KExceptionManager kem) {
        if (moduleContext.getRuleGrammar() != null) {
            return moduleContext.getRuleGrammar();
        } else {
            // TODO: generate the grammar for rules
            CollectTerminalsVisitor ctv = new CollectTerminalsVisitor();
            ctv.visitNode(this);
            for (Module m : getModuleContext().getImportedModules())
                ctv.visitNode(m);

            KSyntax2GrammarStatesFilter generator = new KSyntax2GrammarStatesFilter(ctv, this.getModuleContext().getDeclaredSorts(), kem);
            generator.visitNode(this);
            for (Module m : getModuleContext().getImportedModules())
                generator.visitNode(m);


            return generator.getGrammar();
        }
    }
}
