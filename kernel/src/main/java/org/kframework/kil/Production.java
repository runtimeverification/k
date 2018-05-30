// Copyright (c) 2012-2018 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kore.Sort;

import com.google.common.collect.Multimap;
import org.kframework.utils.StringUtil;

import java.util.List;

/**
 * A production. Any explicit attributes on the production are stored in {@link ASTNode#attributes}.
 */
public class Production extends ASTNode {

    /*
     * Andrei S: It appears that the cons attribute is mandatory for all new production added during compilation, otherwise a null pointer exception can be thrown in one of the later compilation
     * steps.
     */
    protected List<ProductionItem> items;
    protected Sort sort;
    protected String ownerModuleName;
    private Multimap<Integer, Integer> binderMap;

    public boolean isListDecl() {
        return items.size() == 1 && items.get(0) instanceof UserList;
    }

    /**
     * Returns the KLabel for the list terminator.
     * Constructed as '.List{"<list_klabel>"}
     * Should be called only if isListDecl is true.
     * @return String representation of the separator KLabel.
     */
    public String getTerminatorKLabel() {
        assert isListDecl();
        return ".List{" + StringUtil.enquoteCString(getKLabel()) + "}";
    }

    /**
     * True if this production consists of a single nonterminal,
     * even if it has an explicitly assigned label and so is
     * not semantically a subsort declaration.
     * @return
     */
    public boolean isSyntacticSubsort() {
        return items.size() == 1 && items.get(0) instanceof NonTerminal;
    }

    /**
     * True if this production consists is a subsort declaration.
     * It must consist of a single nonterminal, and not have an
     * explicitly assigned label.
     * @return
     */
    public boolean isSubsort() {
        return isSyntacticSubsort() && getKLabel() == null;
    }

    public boolean isLexical() {
        return items.size() == 1 && items.get(0) instanceof Lexical;
    }

    /**
     * Retrieves the {@link Lexical} object of the production if this is a lexical token.
     * Should not be called on other types of productions.
     * @return the Lexical object
     */
    public Lexical getLexical() {
        assert isLexical();
        return (Lexical) items.get(0);
    }

    /**
     * Retrieves the {@link Terminal} object of the production if this is a constant.
     * Should not be called on other types of productions.
     * @return the Terminal object
     */
    public Terminal getConstant() {
        assert isTerminal(); // should be at least a single terminal
        return (Terminal) items.get(0);
    }

    /**
     * Returns true if this production consists of exactly one terminal.
     */
    public boolean isTerminal() {
        return items.size() == 1 && items.get(0) instanceof Terminal;
    }

    public Production(Production node) {
        super(node);
        this.items = node.items;
        this.sort = node.sort;
        this.ownerModuleName = node.ownerModuleName;
    }

    public Production(NonTerminal sort, java.util.List<ProductionItem> items) {
        super();
        this.items = items;
        this.sort = sort.getSort();
    }

    public Production(NonTerminal sort, java.util.List<ProductionItem> items, String ownerModule) {
        super();
        this.items = items;
        this.sort = sort.getSort();
        this.ownerModuleName = ownerModule;
    }

    @Deprecated
    public String getLabel() {
        return getPrefixLabel();
    }

    /**
     * Gets the KLabel corresponding to this production. A production has a
     * KLabel if and only if the production flattens in KORE to a term which is of sort
     * KItem (ie, is a function or a constructor).
     * @return
     */
    public String getKLabel() {
        String klabel = getAttribute("klabel");
        if (klabel == null && (isSyntacticSubsort() || containsAttribute("token") || containsAttribute("bracket"))) {
            return null;
        } else if (klabel == null) {
            klabel = getPrefixLabel();
        }
        return klabel.replace(" ", "");
    }

    private String getPrefixLabel() {
        String label = "";
        for (ProductionItem pi : items) {
            if (pi instanceof NonTerminal) {
                label += "_";
            } else if (pi instanceof Terminal) {
                label += ((Terminal) pi).getTerminal();
            } else if (pi instanceof UserList) {
                label += "_" + ((UserList) pi).separator + "_";
            }
        }
        return label + "_" + ownerModuleName;
    }

    public java.util.List<ProductionItem> getItems() {
        return items;
    }

    public void setItems(java.util.List<ProductionItem> items) {
        this.items = items;
    }

    /**
     * Gets the arity of a production. A production's arity is the number of
     * nonterminals in the syntactic declaration which the production
     * corresponds to.
     * @return
     */
    public int getArity() {
        int arity = 0;
        for (ProductionItem i : items) {
            if (i instanceof UserList)
                arity += 2;
            if (i instanceof NonTerminal)
                arity++;
        }
        return arity;
    }

    public Sort getSort() {
        return sort;
    }

    public void setSort(Sort sort) {
        this.sort = sort;
    }

    public ASTNode getChildNode(int idx) {
        int arity = -1;
        if (items.get(0) instanceof UserList) {
            if (idx == 0) {
                return items.get(0);
            } else {
                return this;
            }
        }
        for (ProductionItem i : items) {
            if (!(i instanceof Terminal))
                arity++;
            if (arity == idx) {
                return i;
            }
        }
        return null;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Production other = (Production) obj;
        if (items == null) {
            if (other.items != null)
                return false;
        } else if (!items.equals(other.items))
            return false;
        if (getKLabel() == null) {
            if (other.getKLabel() != null)
                return false;
        } else if (!getKLabel().equals(other.getKLabel()))
            return false;
        if (sort == null) {
            if (other.sort != null)
                return false;
        } else if (!sort.equals(other.sort))
            return false;
        if (binderMap == null) {
            if (other.binderMap != null)
                return false;
        } else if (!binderMap.equals(other.binderMap))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((items == null) ? 0 : items.hashCode());
        result = prime * result
                + ((getKLabel() == null) ? 0 : getKLabel().hashCode());
        result = prime * result + ((sort == null) ? 0 : sort.hashCode());
        result = prime * result + ((binderMap == null) ? 0 : binderMap.hashCode());
        return result;
    }

    public String toString() {
        String content = "";
        for (ProductionItem i : items)
            content += i + " ";

        return content;
    }

    @Override
    public Production shallowCopy() {
        return new Production(this);
    }

    public void setOwnerModuleName(String ownerModuleName) {
        this.ownerModuleName = ownerModuleName;
    }
}
