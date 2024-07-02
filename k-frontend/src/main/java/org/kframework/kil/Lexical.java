// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.StringUtil;

/** A terminal in a {@link Production}. */
public class Lexical extends ProductionItem {

  private final String lexicalRule;
  private String follow;

  public Lexical(String terminal, String follow) {
    super();
    this.lexicalRule = terminal;
    this.follow = follow;
  }

  @Override
  public void toString(StringBuilder sb) {
    sb.append("r");
    sb.append(StringUtil.enquoteKString(lexicalRule));
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) return false;
    if (obj == this) return true;
    if (!(obj instanceof Lexical trm)) return false;

    return trm.lexicalRule.equals(this.lexicalRule);
  }

  @Override
  public int hashCode() {
    return this.lexicalRule.hashCode();
  }

  public String getLexicalRule() {
    return lexicalRule;
  }
}
