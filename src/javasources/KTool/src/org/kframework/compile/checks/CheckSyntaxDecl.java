// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import java.util.HashMap;
import java.util.List;

import org.kframework.kil.KSorts;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

/**
 * Check for various errors in syntax declarations. 1. You are not allowed to use empty terminals ("") in definitions. You need to have at least two sorts, or a non empty terminal.
 *
 * @author Radu
 *
 */
public class CheckSyntaxDecl extends BasicVisitor {

    public CheckSyntaxDecl(Context context) {
        super(context);
    }

    java.util.Map<Production, Production> prods = new HashMap<Production, Production>();

    @Override
    public Void visit(Production node, Void _) {

        if (prods.containsKey(node)) {
            Production oldProd = prods.get(node);
            String msg = "Production has already been defined at " + oldProd.getLocation() + " in file " + oldProd.getFilename();
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        } else
            prods.put(node, node);

        int sorts = 0;
        int neTerminals = 0;
        int eTerminals = 0;

        if (node.containsAttribute("bracket")) {
            int countSorts = 0;
            for (ProductionItem pi : node.getItems()) {
                if (pi instanceof Sort)
                    countSorts++;
                else if (!(pi instanceof Terminal)) {
                    String msg = "Bracket can be used on productions with Terminals and only one NonTerminal.";
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
                }
            }
            if (countSorts != 1) {
                String msg = "Bracket can be used on productions with Terminals and exactly one NonTerminal.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
        }

        if (node.isSubsort()) {
            String sort = node.getSubsort().getName();
            if (Sort.isBasesort(sort) && !context.isSubsorted(node.getSort(), sort)) {
                String msg = "Subsorting built-in sorts is forbidden: K, KResult, KList, Map,\n\t MapItem, List, ListItem, Set, SetItem, Bag, BagItem, KLabel, CellLabel";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
        } else if (!node.containsAttribute(Constants.FUNCTION)
                && (node.getSort().equals(KSorts.K) ||
                    node.getSort().equals(KSorts.KLIST))) {
            String msg = "Extending sort K or KList is forbidden:\n\t" + node + "\n\tConsider extending KItem instead.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }

        if (node.containsAttribute("reject")) {
            if (node.getItems().size() != 1) {
                String msg = "Only single Terminals can be rejected.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
            if (node.getItems().size() == 1 && !(node.getItems().get(0) instanceof Terminal)) {
                String msg = "Only Terminals can be rejected.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
        }

        for (ProductionItem pi : node.getItems()) {
            if (pi instanceof Sort) {
                sorts++;
                Sort s = (Sort) pi;
                if (!(s.getName().endsWith("CellSort") || s.getName().endsWith("CellFragment")))
                    if (!context.definedSorts.contains(s.getName())) {
                        String msg = "Undefined sort " + s.getName();
                        GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
                    }
                if (s.getName().equals(KSorts.KRESULT) && !(node.isSubsort() && node.getSort().equals(KSorts.KITEM))) {
                    String msg = "KResult is only allowed in the left hand side of syntax.";
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
                }
            }
            if (pi instanceof UserList) {
                sorts++;
                UserList s = (UserList) pi;
                if (!s.getSort().startsWith("#") && !context.definedSorts.contains(s.getSort())) {
                    String msg = "Undefined sort " + s.getSort();
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
                }
                if (s.getSort().equals("KResult")) {
                    String msg = "KResult is only allowed in the left hand side of syntax declarations.";
                    GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), s.getFilename(), s.getLocation()));
                }
            }
            if (pi instanceof Terminal) {
                Terminal t = (Terminal) pi;
                if (t.getTerminal().equals(""))
                    eTerminals++;
                else
                    neTerminals++;
            }
        }

        if (!isBinaryInfixProd(node)) {
            if (node.containsAttribute(Constants.LEFT) || node.containsAttribute(Constants.RIGHT) || node.containsAttribute(Constants.NON_ASSOC)) {
                String msg = "Associativity attribute should only be assigned to binary infix production.\n";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.WARNING, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
        }

        if (eTerminals > 0 && (neTerminals == 0 || sorts < 2))
            if (!node.containsAttribute("onlyLabel") || !node.containsAttribute("klabel")) {
                String msg = "Cannot declare empty terminals in the definition.\n";
                msg += "            Use attribute 'onlyLabel' paired with 'klabel(...)' to limit the use to programs.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
        return null;
    }

    @Override
    public Void visit(Sentence node, Void _) {
        // optimization to not visit the entire tree
        return null;
    }

    private boolean isBinaryInfixProd(Production node) {
        if (node.getArity() != 2) {
            return false;
        }
        List<ProductionItem> prodItems = node.getItems();
        if (prodItems.size() == 2) {
            ProductionItem oprnd1 = node.getItems().get(0);
            ProductionItem oprnd2 = node.getItems().get(1);
            return (oprnd1 instanceof Sort) && (oprnd2 instanceof Sort);
        } else if (prodItems.size() == 3) {
            ProductionItem oprnd1 = node.getItems().get(0);
            ProductionItem op = node.getItems().get(1);
            ProductionItem oprnd2 = node.getItems().get(2);
            return (oprnd1 instanceof Sort) && (oprnd2 instanceof Sort) && (op instanceof Terminal);
        } else {
            return false;
        }
    }
}
