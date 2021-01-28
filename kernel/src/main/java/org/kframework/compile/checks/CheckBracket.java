// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Syntax;
import org.kframework.utils.errorsystem.KEMException;

import java.util.List;
import java.util.stream.Collectors;

public class CheckBracket {

    public static void check(Module m) {
        m.getItems().forEach(CheckBracket::check); // i -> check(i)
    }

    private static void check(ModuleItem i) {
        if (i instanceof Syntax) {
            Syntax s = (Syntax) i;
            for (PriorityBlock b : s.getPriorityBlocks()) {
                for (Production p : b.getProductions()) {
                    if (p.containsAttribute(Att.BRACKET())) {
                        List<ProductionItem> nts = p.getItems().stream().filter(x -> x instanceof NonTerminal).collect(Collectors.toList());
                        if (nts.size() != 1 || !((NonTerminal) nts.get(0)).getSort().equals(s.getDeclaredSort().getSort()))
                            throw KEMException.outerParserError("bracket productions should have exactly one non-terminal of the same sort as the production.", p.getSource(), p.getLocation());
                    }
                }
            }
        }
    }
}
