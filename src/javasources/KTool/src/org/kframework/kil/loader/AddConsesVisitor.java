// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Attribute;
import org.kframework.kil.KSorts;
import org.kframework.kil.Production;
import org.kframework.kil.Terminal;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class AddConsesVisitor extends BasicVisitor {

    public AddConsesVisitor(Context context) {
        super(context);
    }

    public Void visit(Production p, Void _) {
        // add cons to productions that don't have it already
        if (p.containsAttribute("bracket")) {
            // don't add cons to bracket production
            String cons = p.getAttribute("cons");
            String cons2 = StringUtil.escapeSortName(p.getSort()) + "1Bracket";
            if (cons != null) {
                if (!cons.equals(cons2)) {
                    String msg = "Cons must be of the form: '" + cons2 + "'";
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
                }
            } else
                p.putAttribute("cons", cons2);
        } else if (p.getItems().size() == 1
                    && p.getItems().get(0) instanceof Terminal
                    && (p.getSort().startsWith("#")
                || p.getSort().equals(KSorts.KLABEL))) {
            // don't add any cons, if it is a constant
            // a constant is a single terminal for a builtin sort
            String cons = p.getAttribute("cons");
            if (cons != null)
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Constants are not allowed to have cons: '" + cons + "'", p.getFilename(), p.getLocation()));
        } else if (p.isLexical()) {
        } else if (p.isSubsort()) {
            // cons are not allowed for subsortings
            String cons = p.getAttribute("cons");
            if (cons != null && !p.containsAttribute("klabel")) {
                String msg = "Subsortings are not allowed to have cons without klabel: '" + cons + "'";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
            }
            if (p.containsAttribute("klabel") && !p.containsAttribute("cons")) {
                p.putAttribute("cons", StringUtil.escapeSortName(p.getSort()) + "1" + StringUtil.getUniqueId() + "Syn");
            }
        } else {
            if (!p.containsAttribute("cons")) {
                String cons;
                if (p.isListDecl())
                    cons = StringUtil.escapeSortName(p.getSort()) + "1" + "ListSyn";
                else
                    cons = StringUtil.escapeSortName(p.getSort()) + "1" + StringUtil.getUniqueId() + "Syn";
                p.addAttribute(new Attribute("cons", cons));
            } else {
                // check if the provided cons is correct
                String cons = p.getAttribute("cons");
                String escSort = StringUtil.escapeSortName(p.getSort());
                if (!cons.startsWith(escSort)) {
                    String msg = "The cons attribute must start with '" + escSort + "' and not with " + cons;
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
                }
                if (!cons.endsWith("Syn")) { // a normal cons must end with 'Syn'
                    String msg = "The cons attribute must end with 'Syn' and not with " + cons;
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
                }
                if (p.isListDecl() && !cons.endsWith("ListSyn")) { // if this is a list, it must end with 'ListSyn'
                    String msg = "The cons attribute must end with 'ListSyn' and not with " + cons;
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
                }
            }
        }
        return null;
    }
}
