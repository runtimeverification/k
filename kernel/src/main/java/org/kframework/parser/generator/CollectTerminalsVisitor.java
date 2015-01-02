// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.Production;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;

public class CollectTerminalsVisitor extends BasicVisitor {
    public CollectTerminalsVisitor() {
        super(null);
    }

    public Set<Terminal> terminals = new HashSet<>();
    public Set<Production> rejects = new HashSet<>();

    private void addTerminal(Terminal terminal) {
        if (terminal.getTerminal().equals(""))
            return;
        terminals.add(terminal);
    }

    public Void visit(Production p, Void _void) {
        if (p.containsAttribute("reject"))
            rejects.add(p);
        else
            super.visit(p, _void);
        return null;
    }

    public Void visit(Terminal t, Void _void) {
        addTerminal(t);
        return null;
    }

    public Void visit(UserList ul, Void _void) {
        addTerminal(new Terminal(ul.getSeparator()));
        return null;
    }
}
