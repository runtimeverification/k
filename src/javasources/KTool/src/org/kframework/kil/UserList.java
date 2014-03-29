package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;

/**
 * A production item for a cons-list with separator, like List{UserSort,";"}. Must be the only item in a {@link Production}.
 */
public class UserList extends ProductionItem {
    protected String sort;
    protected String separator;
    protected String listType;

    public UserList(String sort, String separator) {
        this.sort = sort;
        this.separator = separator.trim();
        this.listType = "*";
    }

    public UserList(String sort, String separator, String listType) {
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
        if (listType.equals("*"))
            return "List{" + sort + ",\"" + StringUtil.escape(separator) + "\"} ";
        else
            return "NeList{" + sort + ",\"" + StringUtil.escape(separator) + "\"} ";
    }

    public String getTerminatorKLabel() {
        return "'.List{\"" + StringUtil.escape(separator) + "\"}";
    }

    public String getSort() {
        return sort;
    }

    public void setSort(String sort) {
        this.sort = sort;
    }

    public String getSeparator() {
        return separator;
    }

    public void setSeparator(String separator) {
        this.separator = separator.trim();
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
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
