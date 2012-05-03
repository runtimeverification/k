package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.ASTNode;

public class UserList extends ASTNode implements ProductionItem {
	protected String sort;
	protected String separator;

	public UserList(Element element) {
		super(element);

		sort = element.getAttribute(Constants.VALUE_value_ATTR);
		separator = element.getAttribute(Constants.SEPARATOR_separator_ATTR);
	}

	@Override
	public String toString() {
		return "List{" + sort + ",\"" + separator + "\"} ";
	}
}
