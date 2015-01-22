// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import com.google.common.collect.Multimap;

import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KExceptionManager;
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
    protected Sort sort;
    protected String ownerModuleName;
    private Multimap<Integer, Integer> binderMap;

    public static Production makeFunction(Sort funSort, String funName, Sort argSort, org.kframework.kil.loader.Context context) {
        List<ProductionItem> prodItems = new ArrayList<ProductionItem>();
        prodItems.add(new Terminal(funName));
        prodItems.add(new Terminal("("));
        prodItems.add(new NonTerminal(argSort));
        prodItems.add(new Terminal(")"));

        Production funProd = new Production(new NonTerminal(funSort), prodItems);
        if (funSort.isComputationSort()) {
            funProd.putAttribute("klabel", funName);
            context.addProduction(funProd);
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

    /**
     * Returns the KLabel for the list terminator.
     * Constructed as '.List{"<list_klabel>"}
     * Should be called only if isListDecl is true.
     * @return String representation of the separator KLabel.
     */
    public String getTerminatorKLabel() {
        assert isListDecl();
        return "'.List{" + StringUtil.enquoteCString(getKLabel()) + "}";
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

    /**
     * Retrieves the {@link NonTerminal} object of the production if this is a subsorting.
     * Should not be called on other types of productions.
     * @return the Sort object
     */
    public Sort getSubsort() {
        assert isSyntacticSubsort();
        return getChildSort(0);
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
        return isTerminal() && (sort.getName().startsWith("#") || sort.equals(Sort.KLABEL));
    }

    public boolean isConstant(org.kframework.kil.loader.Context context) {
        return isTerminal() && (sort.getName().startsWith("#") ||
                                sort.equals(Sort.KLABEL) ||
                                context.getTokenSorts().contains(getSort()));
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

    public Sort getBracketSort() {
        assert isBracket();
        return getChildSort(0);
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
        if (klabel == null && isSyntacticSubsort()) {
            return null;
        } else if (klabel == null) {
            if (sort.equals(Sort.KLABEL) && getArity() == 0)
                return null;
            else
                klabel = "'" + getPrefixLabel();
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
        return label;
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

    /**
     * Gets the arity of KItems using the KLabel declared by this production.
     * A KItem has the arity of its production, if that production is not
     * a KLabel declaration. KLabel declarations declare KItems with an
     * arity equal to the value of the required integer attribute "arity".
     * @return
     */
    public int getArityOfKItem() {
        if (sort.equals(Sort.KLABEL) && isConstant()) {
            try {
                String attr = getAttribute(Attribute.ARITY_KEY);
                if (attr == null) {
                    throw KExceptionManager.criticalError("Strict KLabels must declare an 'arity' attribute.", this);
                }
                return Integer.parseInt(attr);
            } catch (NumberFormatException e) {
                throw KExceptionManager.criticalError("Could not parse 'arity' attribute as an integer.", e, this);
            }
        }
        return getArity();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
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

    public Sort getChildSort(int idx) {
        ASTNode node = getChildNode(idx);
        if (node instanceof UserList) {
            return ((UserList) node).getSort();
        } else if (node instanceof Production) {
            return ((Production) node).getSort();
        } else if (node instanceof NonTerminal) {
            return ((NonTerminal) node).getSort();
        }
        throw new AssertionError("unreachable");
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
            } else if (item instanceof NonTerminal) {
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
            } else if (item instanceof NonTerminal) {
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
    public List<ProductionItem> getChildren(Enum<?> _void) {
        return items;
    }

    @Override
    public void setChildren(List<ProductionItem> children, Enum<?> _void) {
        this.items = children;
    }

    /**
     * Gets the KLabel which is declared in the definition by this production.
     * A production declares a KLabel if it has a corresponding KLabel (ie,
     * produces a term of sort KItem), or if it is a constant constructor
     * of sort KLabel.
     * @return
     */
    public String getKLabelOfKItem() {
        if (sort.equals(Sort.KLABEL) && isConstant()) {
            return getConstant().getTerminal();
        }
        if (getKLabel() == null) {
            throw KExceptionManager.internalError("Attempted to get null KLabel of production.", this);
        }
        return getKLabel();
    }
}
