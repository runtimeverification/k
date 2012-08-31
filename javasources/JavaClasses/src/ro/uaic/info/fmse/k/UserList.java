package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class UserList extends ProductionItem {
	protected String sort;
	protected String separator;

	public UserList(Element element) {
		super(element);

		sort = element.getAttribute(Constants.VALUE_value_ATTR);
		separator = element.getAttribute(Constants.SEPARATOR_separator_ATTR);
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

	@Override
	public Element toXml(Document doc) {
		Element userlist = doc.createElement(Constants.USERLIST);
		return userlist;
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
	public ASTNode accept(Transformer visitor) {
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
}
