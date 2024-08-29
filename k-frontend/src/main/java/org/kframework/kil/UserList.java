// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kore.Sort;
import org.kframework.utils.StringUtil;

/**
 * A production item for a cons-list with separator, like List{UserSort,";"}. Must be the only item
 * in a {@link Production}.
 */
public class UserList extends ProductionItem {
  protected Sort sort;
  protected String separator;
  protected String listType;

  public static final String ZERO_OR_MORE = "*";
  public static final String ONE_OR_MORE = "+";

  public UserList(Sort sort, String separator) {
    this.sort = sort;
    this.separator = separator;
    this.listType = ZERO_OR_MORE;
  }

  public UserList(Sort sort, String separator, String listType) {
    this.sort = sort;
    this.separator = separator;
    this.listType = listType;
  }

  @Override
  public void toString(StringBuilder sb) {
    if (listType.equals(ZERO_OR_MORE)) {
      sb.append("List{")
          .append(sort)
          .append(",")
          .append(StringUtil.enquoteCString(separator))
          .append("}");
    } else {
      sb.append("NeList{")
          .append(sort)
          .append(",")
          .append(StringUtil.enquoteCString(separator))
          .append("}");
    }
  }

  public Sort getSort() {
    return sort;
  }

  public void setSort(Sort sort) {
    this.sort = sort;
  }

  public String getSeparator() {
    return separator;
  }

  public void setSeparator(String separator) {
    this.separator = separator;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) return false;
    if (obj == this) return true;
    if (!(obj instanceof UserList srt)) return false;

    if (!sort.equals(srt.getSort())) return false;
    return separator.equals(srt.getSeparator());
  }

  @Override
  public int hashCode() {
    return this.separator.hashCode() + this.sort.hashCode();
  }

  public String getListType() {
    return listType;
  }

  public void setListType(String listType) {
    this.listType = listType;
  }
}
