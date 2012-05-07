package ro.uaic.info.fmse.k;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Cell extends Term {
	String label;
	Term contents;
	String sort;
	String elipses;
	Map<String, String> attributes;

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
		contents.accept(visitor);
	}

	public Cell(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.label = element.getAttribute(Constants.LABEL_label_ATTR);
		this.elipses = element.getAttribute(Constants.ELLIPSES_ellipses_ATTR);
		this.contents = (Term) JavaClassesFactory.getTerm(XML
				.getChildrenElements(element).get(0));

		NamedNodeMap its = element.getAttributes();
		attributes = new HashMap<String, String>();

		for (int i = 0; i < its.getLength(); i++) {
			if (!its.item(i).getNodeName()
					.equals(Constants.FILENAME_filename_ATTR)
					&& !its.item(i).getNodeName()
							.equals(Constants.LOC_loc_ATTR)
					&& !its.item(i).getNodeName()
							.equals(Constants.ELLIPSES_ellipses_ATTR)
					&& !its.item(i).getNodeName()
							.equals(Constants.SORT_sort_ATTR)
					&& !its.item(i).getNodeName()
							.equals(Constants.LABEL_label_ATTR)) {
				attributes.put(its.item(i).getNodeName(), its.item(i)
						.getNodeValue());
			}
		}
	}

	public String toString() {
		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet())
			attributes += " " + entry.getKey() + "=\"" + entry.getValue()
					+ "\"";

		String content = "<" + this.label + attributes + ">";

		if (elipses != null && !elipses.equals("none")) {
			if (elipses.equals("left")) {
				content += "... " + this.contents + " ";
			} else if (elipses.equals("right")) {
				content += " " + this.contents + " ...";
			} else if (elipses.equals("both")) {
				content += "... " + this.contents + " ...";
			} else
				content += " " + this.contents;
		}
		return content + "</" + this.label + "> ";
	}

	@Override
	public String toMaude() {
		String labell = "<_>_</_>";

		String head = "", start = "", end = "";
		for (Entry<String, String> entry : attributes.entrySet())
			if (!entry.getValue().equals("")) {
				start += "__(";
				end += ",_=_(" + entry.getKey() + ",\"" + entry.getValue()
						+ "\"))";
			}

		head = start + label + end;

		// TODO: CHECK THIS AGAIN -> THE CONTENTS SHOULD NOT BE NULL
		if (contents != null)
			return labell + "(" + head + ", " + contents.toMaude() + ", "
					+ label + ")";
		return labell + "(" + head + ", " + null + ", " + label + ")";
	}

	public String getLabel() {
		return label;
	}
	
}
