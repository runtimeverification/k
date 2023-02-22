// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.StringUtil;

/** A terminal in a {@link Production}. */
public class Terminal extends ProductionItem {

    private String terminal;

    public Terminal(String terminal) {
        super();
        this.terminal = terminal;
    }

    public void setTerminal(String terminal) {
        this.terminal = terminal;
    }

    public String getTerminal() {
        return terminal;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append(StringUtil.enquoteCString(terminal));
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
}
