// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import com.google.common.collect.Lists;

import java.util.ArrayList;

/**
 * A block of productions at the same priority within a syntax declaration.
 * @see Syntax
 */
public class PriorityBlock extends ASTNode {

    java.util.List<Production> productions = new ArrayList<Production>();
    /** "left", "right", or "non-assoc" if this group of productions had
     * an explicitly declared associativity, "" otherwise */
    String assoc;

    public java.util.List<Production> getProductions() {
        return productions;
    }

    public void setProductions(java.util.List<Production> productions) {
        this.productions = productions;
    }

    public String getAssoc() {
        return assoc;
    }

    public void setAssoc(String assoc) {
        this.assoc = assoc;
    }

    public PriorityBlock() {
        super();
        this.assoc = "";
    }

    public PriorityBlock(String assoc, java.util.List<Production> productions) {
        super();
        this.assoc = assoc;
        this.productions = productions;
    }

    public PriorityBlock(String assoc, Production... productions) {
        this(assoc, Lists.newArrayList(productions));
    }

    @Override
    public void toString(StringBuilder sb) {
        if (!assoc.equals("")) {
            sb.append(assoc).append(": \n    ");
        }
        String conn = "";
        for (Production production : productions) {
            sb.append(conn);
            production.toString(sb);
            conn = "\n  | ";
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (this == obj)
            return true;
        if (!(obj instanceof PriorityBlock))
            return false;
        PriorityBlock pb = (PriorityBlock) obj;

        if (!pb.getAssoc().equals(this.assoc))
            return false;

        if (pb.productions.size() != productions.size())
            return false;

        for (int i = 0; i < pb.productions.size(); i++) {
            if (!pb.productions.get(i).equals(productions.get(i)))
                return false;
        }

        return true;
    }

    @Override
    public int hashCode() {
        int hash = assoc.hashCode();

        for (Production prd : productions)
            hash += prd.hashCode();
        return hash;
    }

}
