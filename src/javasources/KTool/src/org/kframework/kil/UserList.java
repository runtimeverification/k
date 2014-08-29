// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;

/**
 * A production item for a cons-list with separator, like List{UserSort,";"}. Must be the only item in a {@link Production}.
 */
public class UserList extends ProductionItem {
    protected Sort sort;
    protected String separator;
    protected String listType;

    public static final String ZERO_OR_MORE = "*";
    public static final String ONE_OR_MORE = "+";

    public UserList(Sort sort, String separator) {
        this.sort = sort;
        this.separator = separator.trim();
        this.listType = ZERO_OR_MORE;
    }

    public UserList(Sort sort, String separator, String listType) {
        this.sort = sort;
        this.separator = separator.trim();
        this.listType = listType;
    }

    public UserList(UserList userList) {
        super(userList);
        sort = userList.sort;
        separator = userList.separator.trim();
        listType = userList.listType;
    }

    @Override
    public String toString() {
        if (listType.equals(ZERO_OR_MORE))
            return "List{" + sort + "," + StringUtil.enquoteCString(separator) + "} ";
        else
            return "NeList{" + sort + "," + StringUtil.enquoteCString(separator) + "} ";
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
        this.separator = separator.trim();
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
        if (!(obj instanceof UserList))
            return false;

        UserList srt = (UserList) obj;

        if (!sort.equals(srt.getSort()))
            return false;
        if (!separator.equals(srt.getSeparator()))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        return this.separator.hashCode() + this.sort.hashCode();
    }

    @Override
    public UserList shallowCopy() {
        return new UserList(this);
    }

    public String getListType() {
        return listType;
    }

    public void setListType(String listType) {
        this.listType = listType;
    }
}
