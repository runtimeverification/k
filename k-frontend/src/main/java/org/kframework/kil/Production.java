// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil;

import java.util.ArrayList;
import java.util.List;
import org.kframework.attributes.Att;
import org.kframework.kore.Sort;
import org.kframework.utils.StringUtil;

/**
 * A production. Any explicit attributes on the production are stored in {@link
 * ASTNode#getAttributes()}.
 */
public class Production extends ASTNode {

  /*
   * Andrei S: It appears that the cons attribute is mandatory for all new production added during compilation, otherwise a null pointer exception can be thrown in one of the later compilation
   * steps.
   */
  protected List<ProductionItem> items;
  protected Sort sort;
  protected List<Sort> params;
  protected String ownerModuleName;

  public boolean isListDecl() {
    return items.size() == 1 && items.get(0) instanceof UserList;
  }

  /**
   * Returns the symbol for the list terminator.
   *
   * <p>If a label has been specified using `terminator-symbol(...)` then use that; otherwise
   * construct a new label based on the label for the non-terminator production. This new label is
   * constructed as `.List{"<list_klabel>"}`. Should be called only if `isListDecl()` returns true.
   *
   * @return String representation of the terminator symbol.
   */
  public String getTerminatorSymbol(boolean kore) {
    assert isListDecl();

    String terminatorLabel = getAttribute(Att.TERMINATOR_SYMBOL());
    if (terminatorLabel == null) {
      boolean isSymbol = getAttribute(Att.SYMBOL()) != null;
      return ".List{"
          + StringUtil.enquoteCString(getKLabel(kore))
          + "}"
          + (kore && !isSymbol ? "_" + getSort().name() : "");
    }

    return terminatorLabel.replace(" ", "");
  }

  /**
   * True if this production consists of a single nonterminal, even if it has an explicitly assigned
   * label and so is not semantically a subsort declaration.
   *
   * @return
   */
  public boolean isSyntacticSubsort() {
    return items.size() == 1 && items.get(0) instanceof NonTerminal;
  }

  public boolean isLexical() {
    return items.size() == 1 && items.get(0) instanceof Lexical;
  }

  /**
   * Retrieves the {@link Lexical} object of the production if this is a lexical token. Should not
   * be called on other types of productions.
   *
   * @return the Lexical object
   */
  public Lexical getLexical() {
    assert isLexical();
    return (Lexical) items.get(0);
  }

  /**
   * Retrieves the {@link Terminal} object of the production if this is a constant. Should not be
   * called on other types of productions.
   *
   * @return the Terminal object
   */
  public Terminal getConstant() {
    assert isTerminal(); // should be at least a single terminal
    return (Terminal) items.get(0);
  }

  /** Returns true if this production consists of exactly one terminal. */
  public boolean isTerminal() {
    return items.size() == 1 && items.get(0) instanceof Terminal;
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

  /**
   * Gets the effective KLabel declared by the user, taking the `klabel` and `symbol` attributes
   * into account.
   *
   * <p>The effective label is specified as follows:
   *
   * <ul>
   *   <li>If the production has a `symbol(X)` attribute, the effective label is `X`.
   *   <li>If the production has `klabel(X)`, then the effective label is `X`. This syntax will be
   *       deprecated in the future.
   *   <li>Otherwise, return null.
   * </ul>
   *
   * @return A string representing the effective label, or null.
   */
  private String getDeclaredLabel() {
    String symbol = getAttribute(Att.SYMBOL());

    if (symbol != null && !symbol.isEmpty()) {
      return symbol;
    }

    return getAttribute(Att.KLABEL());
  }

  /**
   * Gets the KLabel corresponding to this production. A production has a KLabel if and only if the
   * production flattens in KORE to a term which is of sort KItem (ie, is a function or a
   * constructor).
   *
   * @return
   */
  public String getKLabel(boolean kore) {
    String klabel = getDeclaredLabel();
    if (klabel == null
        && (isSyntacticSubsort()
            || containsAttribute(Att.TOKEN())
            || containsAttribute(Att.BRACKET()))) {
      return null;
    } else if (klabel == null || (kore && getAttribute(Att.SYMBOL()) == null)) {
      klabel = getPrefixLabel(kore);
    }
    return klabel.replace(" ", "");
  }

  public String getBracketLabel(boolean kore) {
    String klabel = getDeclaredLabel();
    if (klabel == null || (kore && getAttribute(Att.SYMBOL()) == null)) {
      klabel = getPrefixLabel(kore);
    }
    return klabel.replace(" ", "");
  }

  private String getPrefixLabel(boolean kore) {
    String label = "";
    List<String> sorts = new ArrayList<>();
    for (ProductionItem pi : items) {
      if (pi instanceof NonTerminal) {
        label += "_";
        sorts.add(((NonTerminal) pi).getSort().name());
      } else if (pi instanceof Terminal) {
        label += ((Terminal) pi).getTerminal();
      } else if (pi instanceof UserList) {
        label += "_" + ((UserList) pi).separator + "_";
        sorts.add(((UserList) pi).sort.name());
        sorts.add(sort.name());
      }
    }
    return label
        + "_"
        + ownerModuleName
        + (kore ? "_" + sorts.stream().reduce(sort.name(), (s1, s2) -> s1 + "_" + s2) : "");
  }

  public java.util.List<ProductionItem> getItems() {
    return items;
  }

  public void setItems(java.util.List<ProductionItem> items) {
    this.items = items;
  }

  /**
   * Gets the arity of a production. A production's arity is the number of nonterminals in the
   * syntactic declaration which the production corresponds to.
   *
   * @return
   */
  public int getArity() {
    int arity = 0;
    for (ProductionItem i : items) {
      if (i instanceof UserList) arity += 2;
      if (i instanceof NonTerminal) arity++;
    }
    return arity;
  }

  public Sort getSort() {
    return sort;
  }

  public void setSort(Sort sort) {
    this.sort = sort;
  }

  public List<Sort> getParams() {
    return params;
  }

  public void setParams(List<Sort> params) {
    this.params = params;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) return true;
    if (obj == null) return false;
    if (getClass() != obj.getClass()) return false;
    Production other = (Production) obj;
    if (items == null) {
      if (other.items != null) return false;
    } else if (!items.equals(other.items)) return false;
    if (getAttribute(Att.KLABEL()) == null) {
      if (other.getAttribute(Att.KLABEL()) != null) return false;
    } else if (!getAttribute(Att.KLABEL()).equals(other.getAttribute(Att.KLABEL()))) return false;
    if (sort == null) {
      if (other.sort != null) return false;
    } else if (!sort.equals(other.sort)) return false;
    return true;
  }

  @Override
  public int hashCode() {
    final int prime = 31;
    int result = 1;
    result = prime * result + ((items == null) ? 0 : items.hashCode());
    result =
        prime * result
            + ((getAttribute(Att.KLABEL()) == null) ? 0 : getAttribute(Att.KLABEL()).hashCode());
    result = prime * result + ((sort == null) ? 0 : sort.hashCode());
    return result;
  }

  @Override
  public void toString(StringBuilder sb) {
    for (ProductionItem i : items) {
      i.toString(sb);
      sb.append(" ");
    }
    sb.append(getAttributes());
  }

  public void setOwnerModuleName(String ownerModuleName) {
    this.ownerModuleName = ownerModuleName;
  }
}
