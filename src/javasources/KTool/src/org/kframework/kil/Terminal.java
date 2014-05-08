// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** A terminal in a {@link Production}. */
public class Terminal extends ProductionItem {

    private String terminal;

    public Terminal(String terminal) {
        super();
        this.terminal = terminal;
    }

    public Terminal(Terminal terminal) {
        super(terminal);
        this.terminal = terminal.terminal;
    }

    public void setTerminal(String terminal) {
        this.terminal = terminal;
    }

    public String getTerminal() {
        return terminal;
    }

    @Override
    public String toString() {
        return "\"" + terminal + "\"";
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof Terminal))
            return false;

        Terminal trm = (Terminal) obj;

        if (!trm.terminal.equals(this.terminal))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return this.terminal.hashCode();
    }

    @Override
    public Terminal shallowCopy() {
        return new Terminal(this);
    }
}
