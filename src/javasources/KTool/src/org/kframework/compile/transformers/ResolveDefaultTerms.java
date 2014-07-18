// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ResolveDefaultTerms extends CopyOnWriteTransformer {

    private Map<String, ConfigurationStructure> config;

    public ResolveDefaultTerms(Context context) {
        super("Resolve Default Terms", context);
        config = context.getConfigurationStructureMap();
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (MetaK.isAnywhere(node)) return node;
        return super.visit(node, _);
    }

    @Override
    public ASTNode visit(Rewrite node, Void _)  {
        ASTNode right = new DefaultTermsResolver(context).visitNode(node.getRight());
        if (right != node.getRight()) {
            node = node.shallowCopy();
            node.setRight((Term)right, context);
        }
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }


    public class DefaultTermsResolver extends CopyOnWriteTransformer {

        public DefaultTermsResolver(Context context) {
            super("Default Terms Resolver", context);
        }

        @Override
        public ASTNode visit(Cell node, Void _)  {
            Cell cell = (Cell) super.visit(node, _);
            if (cell.getEllipses() == Ellipses.NONE) return cell;
            cell = cell.shallowCopy();
            cell.setCellAttributes(new HashMap<String, String>(cell.getCellAttributes()));
            cell.setEllipses(Ellipses.NONE);
            ConfigurationStructure cellStr = config.get(cell.getId());
            if (cellStr.sons.isEmpty()) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.COMPILER,
                        "Cell " + node + " is a leaf in the configuration and it's not closed in the RHS.",
                        getName(), node.getFilename(), node.getLocation()));

                return cell;
            }
            List<Cell> sons = MetaK.getTopCells(cell.getContents(), context);
            Map<String, ConfigurationStructure> potentialSons = new HashMap<String, ConfigurationStructure>(cellStr.sons);

            for (Cell son : sons) {
                ConfigurationStructure sonCfg = potentialSons.get(son.getId());
                if (sonCfg != null && (sonCfg.multiplicity == Multiplicity.ONE || sonCfg.multiplicity == Multiplicity.SOME))
                        potentialSons.remove(son.getId());
            }

            if (potentialSons.isEmpty()) return cell;

            Bag bag;
            if (cell.getContents() instanceof Bag) {
                bag = (Bag) cell.getContents().shallowCopy();
                bag.setContents(new ArrayList<Term>(bag.getContents()));
            } else {
                bag = new Bag();
                bag.getContents().add(cell.getContents());
            }
            boolean change = false;
            for (ConfigurationStructure sonCfg : potentialSons.values()) {
                if (sonCfg.multiplicity == Multiplicity.ONE || sonCfg.multiplicity == Multiplicity.SOME) {
                    Cell son = sonCfg.cell.shallowCopy();
                    son.setCellAttributes(new HashMap<String, String>());
                    if (! sonCfg.sons.isEmpty()) {
                        son.setContents(new Bag());
                        son.setEllipses(Ellipses.BOTH);
                        son = (Cell)visit(son, _);
                    }
                    bag.getContents().add(son);
                    change = true;
                }
            }
            if (change) {
                cell.setContents(bag);
            }
            return cell;
        }


    }

}
