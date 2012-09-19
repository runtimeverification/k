package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


public class UserList extends ProductionItem {
	protected String sort;
	protected String separator;

	public UserList(Element element) {
		super(element);

		sort = element.getAttribute(Constants.VALUE_value_ATTR);
		separator = element.getAttribute(Constants.SEPARATOR_separator_ATTR);
	}

	public UserList(UserList userList) {
		super(userList);
		sort = userList.sort;
		separator = userList.separator;
	}

	public ProductionType getType() {
		return ProductionType.USERLIST;
	}

	@Override
	public String toString() {
		return "List{" + sort + ",\"" + separator + "\"} ";
	}

	@Override
	public String toMaude() {
		return "";
	}

	public void accept(Modifier visitor) {
		visitor.modify(this);
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
		this.separator = separator;
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
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
}
