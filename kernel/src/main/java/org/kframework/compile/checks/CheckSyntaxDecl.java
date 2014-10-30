// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import java.util.HashMap;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KExceptionManager;

/**
 * Check for various errors in syntax declarations. 1. You are not allowed to use empty terminals ("") in definitions. You need to have at least two sorts, or a non empty terminal.
 *
 * @author Radu
 *
 */
public class CheckSyntaxDecl extends BasicVisitor {

    private final KExceptionManager kem;

    public CheckSyntaxDecl(Context context, KExceptionManager kem) {
        super(context);
        this.kem = kem;
    }

    java.util.Map<Production, Production> prods = new HashMap<Production, Production>();

    @Override
    public Void visit(Production node, Void _) {

        if (prods.containsKey(node)) {
            Production oldProd = prods.get(node);
            String msg = "Production has already been defined at " + oldProd.getLocation() + " from source " + oldProd.getSource();
            throw KExceptionManager.compilerError(msg, this, node);
        } else
            prods.put(node, node);

        int sorts = 0;
        int neTerminals = 0;
        int eTerminals = 0;

        if (node.containsAttribute("bracket")) {
            int countSorts = 0;
            for (ProductionItem pi : node.getItems()) {
                if (pi instanceof NonTerminal)
                    countSorts++;
                else if (!(pi instanceof Terminal)) {
                    String msg = "Bracket can be used on productions with Terminals and only one NonTerminal.";
                    throw KExceptionManager.compilerError(msg, this, node);
                }
            }
            if (countSorts != 1) {
                String msg = "Bracket can be used on productions with Terminals and exactly one NonTerminal.";
                throw KExceptionManager.compilerError(msg, this, node);
            }
        }

        if (node.isSubsort()) {
            Sort sort = node.getSubsort();
            if (sort.isBaseSort() && !context.isSubsorted(node.getSort(), sort)) {
                String msg = "Subsorting built-in sorts is forbidden: K, KResult, KList, Map,\n\t MapItem, List, ListItem, Set, SetItem, Bag, BagItem, KLabel, CellLabel";
                throw KExceptionManager.compilerError(msg, this, node);
            }
        } else if (!node.containsAttribute(Constants.FUNCTION)
                && (node.getSort().equals(Sort.K) ||
                    node.getSort().equals(Sort.KLIST))) {
            String msg = "Extending sort K or KList is forbidden:\n\t" + node + "\n\tConsider extending KItem instead.";
            throw KExceptionManager.compilerError(msg, this, node);
        }

        if (node.containsAttribute("reject")) {
            if (node.getItems().size() != 1) {
                String msg = "Only single Terminals can be rejected.";
                throw KExceptionManager.compilerError(msg, this, node);
            }
            if (node.getItems().size() == 1 && !(node.getItems().get(0) instanceof Terminal)) {
                String msg = "Only Terminals can be rejected.";
                throw KExceptionManager.compilerError(msg, this, node);
            }
        }

        for (ProductionItem pi : node.getItems()) {
            if (pi instanceof NonTerminal) {
                sorts++;
                NonTerminal s = (NonTerminal) pi;
                if (!s.getSort().isCellSort()) {
                    if (!context.definedSorts.contains(s.getSort())) {
                        String msg = "Undefined sort " + s;
                        throw KExceptionManager.compilerError(msg, this, s);
                    }
                }
                if (s.getSort().equals(Sort.KRESULT) && !(node.isSubsort() && node.getSort().equals(Sort.KITEM))) {
                    String msg = "KResult is only allowed in the left hand side of syntax.";
                    throw KExceptionManager.compilerError(msg, this, s);
                }
            }
            if (pi instanceof UserList) {
                sorts++;
                UserList s = (UserList) pi;
                if (!s.getSort().getName().startsWith("#") && !context.definedSorts.contains(s.getSort())) {
                    String msg = "Undefined sort " + s.getSort();
                    throw KExceptionManager.compilerError(msg, this, s);
                }
                if (s.getSort().equals(Sort.KRESULT)) {
                    String msg = "KResult is only allowed in the left hand side of syntax declarations.";
                    throw KExceptionManager.compilerError(msg, this, s);
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

        if (!(node.getItems().get(0) instanceof NonTerminal) && node.containsAttribute(Constants.RIGHT)) {
            String msg = "'" + Constants.RIGHT + "' should be used only on productions which start with a NonTerminal.\n";
            kem.registerCompilerWarning(msg, this, node);
        }

        if (!(node.getItems().get(node.getItems().size() - 1) instanceof NonTerminal) && node.containsAttribute(Constants.LEFT)) {
            String msg = "'" + Constants.LEFT + "' should be used only on productions which end with a NonTerminal.\n";
            kem.registerCompilerWarning(msg, this, node);
        }

        if (eTerminals > 0 && (neTerminals == 0 || sorts < 2)) {
            // if it is an epsilon transition, it must contain a klabel and one of:
            // onlyLabel or (notInRules, notInGround)
            if (!((node.containsAttribute("onlyLabel") ||
                    (node.containsAttribute("notInRules") && node.containsAttribute("notInGround")))
                    && node.containsAttribute("klabel"))) {
                String msg = "Cannot declare empty terminals in the definition.\n";
                msg += "        Use attribute 'onlyLabel', or both 'notInRules' and 'notInGround'\n";
                msg += "        paired with 'klabel(...)' to limit the use to programs.";
                throw KExceptionManager.compilerError(msg, this, node);
            }
        }
        return null;
    }

    @Override
    public Void visit(Sentence node, Void _) {
        // optimization to not visit the entire tree
        return null;
    }
}
