// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.StringUtil;

/** A terminal in a {@link Production}. */
public class Lexical extends ProductionItem {

    private String lexicalRule;
    private String follow;

    public Lexical(String terminal, String follow) {
        super();
        this.lexicalRule = terminal;
        this.follow = follow;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("r");
        sb.append(StringUtil.enquoteCString(lexicalRule));
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof Lexical))
            return false;

        Lexical trm = (Lexical) obj;

        if (!trm.lexicalRule.equals(this.lexicalRule))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return this.lexicalRule.hashCode();
    }

    public void setFollow(String follow) {
        this.follow = follow;
    }

    public String getFollow() {
        return follow;
    }

    public String getLexicalRule() {
        return lexicalRule;
    }

}
