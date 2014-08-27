// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.Production;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;

public class CollectTerminalsVisitor extends BasicVisitor {
    public CollectTerminalsVisitor(Context context) {
        super(context);
    }

    public Set<Terminal> terminals = new HashSet<>();
    public Set<Production> rejects = new HashSet<>();

    private void addTerminal(Terminal terminal) {
        if (terminal.getTerminal().equals(""))
            return;
        terminals.add(terminal);
    }

    public Void visit(Production p, Void _) {
        if (p.containsAttribute("reject"))
            rejects.add(p);
        else
            super.visit(p, _);
        return null;
    }

    public Void visit(Terminal t, Void _) {
        addTerminal(t);
        return null;
    }

    public Void visit(UserList ul, Void _) {
        addTerminal(new Terminal(ul.getSeparator()));
        return null;
    }
}
