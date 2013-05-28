package org.kframework.backend.symbolic;

import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.Iterator;
import java.util.Set;

/**
 * Check if a term can be translated into SMTLIB by verifying if the
 * corresponding syntax production has the attribute 'smtlib'.
 *
 * @author andreiarusoaie
 */
public class CheckSmtlibVisitor extends BasicVisitor {

    private boolean smtValid = false;

    public CheckSmtlibVisitor(Context context) {
        super("Check SMTLIB translation.", context);
    }

    public boolean smtValid() {
        return smtValid;
    }

    @Override
    public void visit(KApp node) {
        Term klabel = node.getLabel();

        if (klabel instanceof KLabelConstant) {
            if (klabel.equals(KLabelConstant.KEQ)) {
                smtValid = true;
                return;
            }

            Set<Production> prods = context.productions.get(((KLabelConstant) klabel).getLabel());
            if (prods == null) {
                smtValid = false;
            } else {
                Iterator<Production> it = prods.iterator();
                while (it.hasNext()) {
                    Production p = it.next();
                    if (p.containsAttribute("smtlib") || p.containsAttribute("symbolic-function")) {
                        smtValid = true;
                    }
                    else {
                        smtValid = false;
                    }
                    // only first production assumed
                    break;
                }
            }
        }
        super.visit(node);
    }
}
