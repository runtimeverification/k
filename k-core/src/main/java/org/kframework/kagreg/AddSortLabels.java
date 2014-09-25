// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kagreg;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/*
 * Add to each sort a labeled production for that sort.
 *
 * E.g. transform
 * syntax Exp ::= Id
 *              | Exp "+" Exp into
 * syntax Exp ::= Id
 *                 | Exp "+" Exp
 *              | "LExp" Id ":" Exp
 *
 * If multiple syntax declarations for the same sort appear, makes sure only one is changed.
 */
public class AddSortLabels extends CopyOnWriteTransformer {

    /*
     * list of sorts already labeled, when encountered again ignore.
     */
    final protected List<Sort> labeledSorts;

    public AddSortLabels(Context context, List<Sort> labeledSorts) {
        super("AddSortLabels", context);
        this.labeledSorts = labeledSorts;
    }

    @Override
    public ASTNode visit(Module module, Void _)  {
        if (module.isPredefined()) {
            return module;
        }
        return super.visit(module, _);
    }

    @Override
    public ASTNode visit(Syntax syntax, Void _)  {
        if (labeledSorts.contains(syntax.getDeclaredSort().getSort())) {
            return syntax;
        }
        labeledSorts.add(syntax.getDeclaredSort().getSort());
        List<ProductionItem> productionItems = new ArrayList<ProductionItem>();
        productionItems.add(new Terminal("L" + syntax.getDeclaredSort()));
        productionItems.add(new NonTerminal(Sort.ID));
        productionItems.add(new Terminal(":"));
        productionItems.add(syntax.getDeclaredSort());
        Production production = new Production(syntax.getDeclaredSort(), productionItems);

//        System.out.println("Before: " + context.conses);
//        System.out.println("After: " + context.conses);
//        acv.visit(production);
        List<PriorityBlock> priorityBlocks = syntax.getPriorityBlocks();
        if (priorityBlocks.size() == 0) {
//            System.out.println(syntax.getSort() + " empty priorityBlocks");
            PriorityBlock priorityBlock = new PriorityBlock();
            List<Production> productions = new ArrayList<Production>();
            productions.add(production);
            priorityBlock.setProductions(productions);
            priorityBlocks.add(priorityBlock);
        } else {
            priorityBlocks.get(priorityBlocks.size() - 1).getProductions().add(production);
        }
        syntax.setPriorityBlocks(priorityBlocks);
        return syntax;
    }
}
