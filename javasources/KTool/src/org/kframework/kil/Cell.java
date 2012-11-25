package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

public class Cell extends Term {
	public enum Multiplicity {
		ONE, MAYBE, ANY, SOME,
	}

	public enum Ellipses {
		LEFT, RIGHT, BOTH, NONE,
	}

	String label;
	Term contents;
	Map<String, String> cellAttributes;

	public Cell(String location, String filename) {
		super(location, filename, "BagItem");
		cellAttributes = new HashMap<String, String>();
	}

	public Cell(Element element) {
		super(element);
		this.sort = "BagItem";
		this.label = element.getAttribute(Constants.LABEL_label_ATTR);
		this.contents = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));

		NamedNodeMap its = element.getAttributes();
		cellAttributes = new HashMap<String, String>();
		setEllipses(element.getAttribute(Constants.ELLIPSES_ellipses_ATTR));

		for (int i = 0; i < its.getLength(); i++) {
			if (!its.item(i).getNodeName().equals(Constants.FILENAME_filename_ATTR) && !its.item(i).getNodeName().equals(Constants.LOC_loc_ATTR) // &&
																																					// !its.item(i).getNodeName().equals(Constants.ELLIPSES_ellipses_ATTR)
					&& !its.item(i).getNodeName().equals(Constants.SORT_sort_ATTR) && !its.item(i).getNodeName().equals(Constants.LABEL_label_ATTR)) {
				cellAttributes.put(its.item(i).getNodeName(), its.item(i).getNodeValue());
			}
		}
	}

	public Cell(Cell node) {
		super(node);
		this.label = node.label;
		this.cellAttributes = node.cellAttributes;
		this.contents = node.contents;
	}

	public Cell() {
		super("BagItem");
		cellAttributes = new HashMap<String, String>();
	}

	public boolean hasRightEllipsis() {
		Ellipses e = getEllipses();
		return (e == Ellipses.RIGHT || e == Ellipses.BOTH);
	}

	public boolean hasLeftEllipsis() {
		Ellipses e = getEllipses();
		return (e == Ellipses.LEFT || e == Ellipses.BOTH);
	}

	@Override
	public String toString() {
		String attributes = "";
		for (Entry<String, String> entry : this.cellAttributes.entrySet())
			attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";

		String content = "<" + this.label + attributes + ">";

		if (hasLeftEllipsis())
			content += "...";
		content += " " + this.contents + " ";
		if (hasRightEllipsis())
			content += "...";

		return content + "</" + this.label + "> ";
	}

	public String getLabel() {
		return label;
	}

	public Term getContents() {
		return contents;
	}

	public void setContents(Term contents) {
		this.contents = contents;
	}

	public String getSort() {
		return sort;
	}

	public void setSort(String sort) {
		this.sort = sort;
	}

	public Multiplicity getMultiplicity() {
		if (cellAttributes.containsKey("multiplicity")) {
			String attr = cellAttributes.get("multiplicity");
			if ("?".equals(attr))
				return Multiplicity.MAYBE;
			if ("*".equals(attr))
				return Multiplicity.ANY;
			if ("+".equals(attr))
				return Multiplicity.SOME;
			if ("1".equals(attr))
				return Multiplicity.ONE;
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "Unknown multiplicity in configuration for cell " + this.getLabel() + ".", this.getFilename(),
					this.getLocation()));
		}
		return Multiplicity.ONE;
	}

	public Ellipses getEllipses() {
		String attr = cellAttributes.get("ellipses");
		try {
			if (attr != null) {
				return Ellipses.valueOf(attr.toUpperCase());
			}
		} catch (IllegalArgumentException e) {
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "Unknown ellipses value in configuration for cell " + this.getLabel() + ". Assuming none.",
					this.getFilename(), this.getLocation()));
		}
		return Ellipses.NONE;
	}

	public void setEllipses(String ellipses) {
		ellipses = ellipses.toLowerCase();
		if (ellipses.isEmpty() || ellipses.equals("none")) {
			cellAttributes.remove("ellipses");
		} else
			cellAttributes.put("ellipses", ellipses);
	}

	public Map<String, String> getCellAttributes() {
		return cellAttributes;
	}

	public void setCellAttributes(Map<String, String> cellAttributes) {
		this.cellAttributes = cellAttributes;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	public void setDefaultAttributes() {
		cellAttributes = new HashMap<String, String>();
	}

	@Override
	public Cell shallowCopy() {
		return new Cell(this);
	}

	public String getId() {
		String id = cellAttributes.get("id");
		if (null == id)
			id = this.label;
		return id;
	}

	public void setEllipses(Ellipses e) {
		setEllipses(e.toString());
	}

	public void setId(String id) {
		if (getId().equals(id))
			return;
		cellAttributes.put("id", id);
	}
}
