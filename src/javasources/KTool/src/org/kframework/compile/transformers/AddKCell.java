// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import java.util.*;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddKCell extends CopyOnWriteTransformer {
    /*
     * Stores the list of cells that contain komputations. By default, contains only the "k" cell.
     */
    protected java.util.List<String> komputationCells;

    /*
     * Used to remember for each module the rules that need to be added.
     */
    protected java.util.List<ModuleItem> newRules;

    public AddKCell(Context context) {
        super("Add K cell", context);
        this.komputationCells = new ArrayList<String>();
        if (context.getKomputationCells() == null) {
            this.komputationCells.add("k");
        } else {
            this.komputationCells = context.getKomputationCells();
        }
        assert !this.komputationCells.isEmpty();
    }

    @Override
    public ASTNode visit(Module module, Void _)  {
        newRules = new ArrayList<ModuleItem>();
        Module newModule = (Module)super.visit(module, _);
        Module returnModule;
        if (newRules.isEmpty()) {
            returnModule = newModule;
        } else {
            returnModule = newModule.shallowCopy();
            returnModule = returnModule.addModuleItems(newRules);
        }
        return returnModule;
    }

    @Override
    public ASTNode visit(Rule node, Void _) {
        if (MetaK.isAnywhere(node)) {
            return node;
        }

        if (!MetaK.isComputationSort(node.getBody().getSort())) {
            return node;
        }
        node = node.shallowCopy();
        String computationCellsAttr = node.getAttribute(Attribute.CELL_KEY);
        List<String> computationCells;
        if (computationCellsAttr != null) {
            computationCells = new ArrayList<>();
            Collections.addAll(computationCells, computationCellsAttr.split(","));
        } else {
            computationCells = komputationCells;
        }
        for (int i = 1; i < computationCells.size(); ++i) {
            // first all other rules are scheduled to be added
            Rule newRule = node.shallowCopy();
            newRule.setBody(MetaK.kWrap(node.getBody(), this.komputationCells.get(i)));
            newRules.add(newRule);
        }
        assert !computationCells.isEmpty();
        node.setBody(MetaK.kWrap(node.getBody(), computationCells.get(0))); // then first rule replaces older rule

        return node;
    }

    @Override
    public ASTNode visit(Configuration cfg, Void _)  {
        if (!intersects(MetaK.getAllCellLabels(cfg.getBody(), context), komputationCells)) {
            cfg = cfg.shallowCopy();
            Bag bag;
            if (cfg.getBody() instanceof Bag) {
                bag = (Bag) cfg.getBody().shallowCopy();
            } else {
                bag = new Bag();
                bag.getContents().add(cfg.getBody());
            }
            cfg.setBody(bag);
            for (String kCell : komputationCells) {
                Cell k = new Cell();
                k.setLabel(kCell);
                k.setEllipses(Ellipses.NONE);
                k.setContents(KSequence.EMPTY);
                bag.getContents().add(k);
            }
        }

        return cfg;
    }

    private static boolean intersects(List<String> l1, List<String> l2) {
        for (String s1 : l1) {
            if (l2.contains(s1)) {
                return true;
            }
        }
        return false;
    }
}
