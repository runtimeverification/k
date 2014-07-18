// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import com.google.common.collect.Multimap;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.visitors.Visitor;

import java.util.ArrayList;
import java.util.List;

/**
 * A production. Any explicit attributes on the production are stored in {@link ASTNode#attributes}.
 */
public class Production extends ASTNode implements Interfaces.MutableList<ProductionItem, Enum<?>> {

    /*
     * Andrei S: It appears that the cons attribute is mandatory for all new production added during compilation, otherwise a null pointer exception can be thrown in one of the later compilation
     * steps.
     */
    protected List<ProductionItem> items;
    protected String sort;
    protected String ownerModuleName;
    private Multimap<Integer, Integer> binderMap;

    public static Production makeFunction(String funSort, String funName, String argSort, org.kframework.kil.loader.Context context) {
        List<ProductionItem> prodItems = new ArrayList<ProductionItem>();
        prodItems.add(new Terminal(funName));
        prodItems.add(new Terminal("("));
        prodItems.add(new Sort(argSort));
        prodItems.add(new Terminal(")"));

        Production funProd = new Production(new Sort(funSort), prodItems);
        funProd.addAttribute(new Attribute("prefixlabel", funName));
        if (MetaK.isComputationSort(funSort)) {
            funProd.addAttribute(new Attribute("klabel", funName));
            String consAttr = funSort + "1" + funName + "Syn";
            funProd.addAttribute(new Attribute("cons", consAttr));
            context.conses.put(consAttr, funProd);
            context.putLabel(funProd, consAttr);
        }

        return funProd;
    }

    public boolean isListDecl() {
        return items.size() == 1 && items.get(0) instanceof UserList;
    }

    /**
     * Retrieves the {@link UserList} object of the production if this is a list declaration.
     * Should not be called on other types of productions.
     * @return the list object
     */
    public UserList getListDecl() {
        assert isListDecl();
        return (UserList) items.get(0);
    }

    public boolean isSubsort() {
        return items.size() == 1 && items.get(0) instanceof Sort;
    }

    /**
     * Retrieves the {@link Sort} object of the production if this is a subsorting.
     * Should not be called on other types of productions.
     * @return the Sort object
     */
    public Sort getSubsort() {
        assert isSubsort();
        return (Sort) items.get(0);
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

    public boolean isConstant() {
        // TODO(Radu): properly determine if a production is a constant or not, just like below
        return isTerminal() && (sort.startsWith("#") || sort.equals(KSorts.KLABEL));
    }

    public boolean isConstant(org.kframework.kil.loader.Context context) {
        return isTerminal() && (sort.startsWith("#") ||
                                sort.equals(KSorts.KLABEL) ||
                                context.getTokenSorts().contains(this.getSort()));
    }

    public boolean isBracket() {
        return getArity() == 1 && getAttribute(Attribute.BRACKET.getKey()) != null;
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

    public String getBracketSort() {
        assert isBracket();
        return getChildSort(0);
    }

    public Production(Production node) {
        super(node);
        this.items = node.items;
        this.sort = node.sort;
        this.ownerModuleName = node.ownerModuleName;
    }

    public Production(Sort sort, java.util.List<ProductionItem> items) {
        super();
        this.items = items;
        this.sort = sort.getName();
        attributes = new Attributes();
    }

    public Production(Sort sort, java.util.List<ProductionItem> items, String ownerModule) {
        super();
        this.items = items;
        this.sort = sort.getName();
        attributes = new Attributes();
        this.ownerModuleName = ownerModule;
    }

    public String getCons() {
        return attributes.get("cons");
    }

    /**
     * Use .getKLabel() if you want the klabel
     */
    @Deprecated
    public String getLabel() {
        String label = attributes.get("prefixlabel");
        if (label == null) {
            label = getPrefixLabel();
            attributes.set("prefixlabel", label);
        }
        return label.replace(" ", "");
    }

    public String getKLabel() {
        /*
        assert MetaK.isComputationSort(sort) || sort.equals(KSorts.KLABEL) && isConstant():
                sort + " ::= " + this + " -> " + getPrefixLabel();
        */

        String klabel = attributes.get("klabel");
        if (klabel == null) {
            if (sort.toString().equals(KSorts.KLABEL))
                klabel = getPrefixLabel();
            else
                klabel = "'" + getPrefixLabel();
            attributes.set("klabel", klabel);
        }
        return klabel.replace(" ", "");
    }

    private String getPrefixLabel() {
        String label = "";
        for (ProductionItem pi : items) {
            if (pi instanceof Sort) {
                label += "_";
            } else if (pi instanceof Terminal) {
                label += ((Terminal) pi).getTerminal();
            } else if (pi instanceof UserList) {
                label += "_" + ((UserList) pi).separator + "_";
            }
        }
        return label;
    }

    public java.util.List<ProductionItem> getItems() {
        return items;
    }

    public void setItems(java.util.List<ProductionItem> items) {
        this.items = items;
    }

    public int getArity() {
        int arity = 0;
        for (ProductionItem i : items) {
            if (i instanceof UserList)
                arity += 2;
            if (i instanceof Sort)
                arity++;
        }
        return arity;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    public String getSort() {
        return sort;
    }

    public void setSort(String sort) {
        this.sort = sort;
    }

    public String getChildSort(int idx) {
        int arity = -1;
        if (items.get(0) instanceof UserList) {
            if (idx == 0) {
                return ((UserList) items.get(0)).getSort();
            } else {
                return this.getSort();
            }
        }
        for (ProductionItem i : items) {
            if (!(i instanceof Terminal))
                arity++;
            if (arity == idx) {
                return ((Sort) i).getName();
            }
        }
        return null;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (!(obj instanceof Production))
            return false;
        Production prd = (Production) obj;

        if (this.sort != null && prd.getSort() != null)
            if (!this.sort.equals(prd.getSort()))
                return false;
        if (this.sort == null && prd.getSort() != null)
            return false;

        if (prd.getItems().size() != this.items.size())
            return false;

        for (int i = 0; i < this.items.size(); i++) {
            if (!prd.getItems().get(i).equals(items.get(i)))
                return false;
        }
        String klabel1 = prd.getAttributes().get("klabel");
        String klabel2 = getAttributes().get("klabel");
        if ((klabel1 == null && klabel2 != null) || (klabel1 != null && klabel2 == null)) {
            return false;
        }
        if (klabel1 != null && klabel2 != null && klabel1.equals(klabel2)) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        int hash = 0;
        if (sort != null)
            hash += sort.hashCode();

        for (ProductionItem pi : this.items)
            hash += pi.hashCode();
        return hash;
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

    public String getOwnerModuleName() {
        return ownerModuleName;
    }

    public void setOwnerModuleName(String ownerModuleName) {
        this.ownerModuleName = ownerModuleName;
    }

    public boolean hasTerminalToRight(int idx) {
        int arity = 0;
        for (int i = 0; i < items.size(); i++) {
            ProductionItem item = items.get(i);
            if (item instanceof UserList) {
                if (idx == arity)
                    return !((UserList) item).getSeparator().equals("");
                if (idx == arity + 1)
                    return false;
                arity += 2;
            } else if (item instanceof Sort) {
                if (idx == arity)
                    return i != items.size() - 1 && items.get(i + 1) instanceof Terminal;
                arity++;
            }
        }
        throw new IllegalArgumentException("Index not found in production");
    }

    public boolean hasTerminalToLeft(int idx) {
        int arity = 0;
        for (int i = 0; i < items.size(); i++) {
            ProductionItem item = items.get(i);
            if (item instanceof UserList) {
                if (idx == arity)
                    return false;
                if (idx == arity + 1)
                    return !((UserList) item).getSeparator().equals("");
                arity += 2;
            } else if (item instanceof Sort) {
                if (idx == arity)
                    return i != 0 && items.get(i - 1) instanceof Terminal;
                arity++;
            }
        }
        throw new IllegalArgumentException("Index not found in production");
    }

    /**
     * Getter for the {@code binderMap} structure.
     * The binder map is a MultiMap consisting of key -> value pairs
     * representing the position of a bounded variable and the position
     * of an expression in which it is bound.
     *
     * Important note:  Unlike the positions specified by user (which start at 1),
     * the positions in binderMap are rebased to start at 0 as it
     * is customary for Java collections.
     *
     * @return the binder map associated to this production
     */
    public Multimap<Integer, Integer> getBinderMap() {
        return binderMap;
    }

    public void setBinderMap(Multimap<Integer, Integer> binderMap) {
        this.binderMap = binderMap;
    }

    @Override
    public List<ProductionItem> getChildren(Enum<?> _) {
        return items;
    }

    @Override
    public void setChildren(List<ProductionItem> children, Enum<?> _) {
        this.items = children;
    }
}
