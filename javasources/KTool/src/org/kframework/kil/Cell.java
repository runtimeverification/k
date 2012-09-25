package org.kframework.kil;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.utils.xml.XML;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;


public class Cell extends Term {
	public enum Multiplicity {
		ONE,
		MAYBE,
		ANY,
		SOME,
	}
	
	String label;
	Term contents;
	String ellipses;
	Map<String, String> attributes;

	public Cell(String location, String filename) {
		super(location, filename, "BagItem");
		attributes = new HashMap<String, String>();
	}

	public Cell(Element element) {
		super(element);
		this.sort = "BagItem";
		this.label = element.getAttribute(Constants.LABEL_label_ATTR);
		this.ellipses = element.getAttribute(Constants.ELLIPSES_ellipses_ATTR);
		this.contents = (Term) JavaClassesFactory.getTerm(XML.getChildrenElements(element).get(0));

		NamedNodeMap its = element.getAttributes();
		attributes = new HashMap<String, String>();

		for (int i = 0; i < its.getLength(); i++) {
			if (!its.item(i).getNodeName().equals(Constants.FILENAME_filename_ATTR) && !its.item(i).getNodeName().equals(Constants.LOC_loc_ATTR) // && !its.item(i).getNodeName().equals(Constants.ELLIPSES_ellipses_ATTR)
					&& !its.item(i).getNodeName().equals(Constants.SORT_sort_ATTR) && !its.item(i).getNodeName().equals(Constants.LABEL_label_ATTR)) {
				attributes.put(its.item(i).getNodeName(), its.item(i).getNodeValue());
			}
		}
	}

	public Cell(Cell node) {
		super(node);
		this.label = node.label;
		this.attributes = node.attributes;
		this.ellipses = node.ellipses;
		this.contents = node.contents;
	}

	public Cell() {
		super("BagItem");
		attributes = new HashMap<String, String>();
	}

	public boolean hasRightEllipsis() {
		return ellipses != null &&
				(ellipses.equals("right") || ellipses.equals("both"));
	}

	public boolean hasLeftEllipsis() {
		return ellipses != null &&
				(ellipses.equals("left") || ellipses.equals("both"));
	}

	@Override
	public String toString() {
		String attributes = "";
		for (Entry<String, String> entry : this.attributes.entrySet())
			attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";

				String content = "<" + this.label + attributes + ">";

				if (ellipses != null && !ellipses.equals("none")) {
					if (ellipses.equals("left")) {
						content += "... " + this.contents + " ";
					} else if (ellipses.equals("right")) {
						content += " " + this.contents + " ...";
					} else if (ellipses.equals("both")) {
						content += "... " + this.contents + " ...";
					}

				} else {
					content += " " + this.contents;
				}
				return content + "</" + this.label + "> ";
	}

	@Override
	public String toMaude() {
		String labell = "<_>_</_>";

		String head = "", start = "", end = "";
//		System.out.println(attributes.entrySet());
		for (Entry<String, String> entry : attributes.entrySet())
			if (!entry.getValue().equals("")) {
				start += "__(";
				end += ",_=_(" + entry.getKey() + ",\"" + entry.getValue() + "\"))";
			}

		head = start + label + end;

		// TODO: CHECK THIS AGAIN -> THE CONTENTS SHOULD NOT BE NULL
		if (contents != null) {
//			System.out.println(labell + "(" + head + ", " + contents.toMaude() + ", " + label + ")");
			return labell + "(" + head + ", " + contents.toMaude() + ", " + label + ")";
		}
		return labell + "(" + head + ", " + null + ", " + label + ")";
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
		if (attributes.containsKey("multiplicity")) {	
			String attr = attributes.get("multiplicity");
			if ("?".equals(attr)) return Multiplicity.MAYBE;
			if ("*".equals(attr)) return Multiplicity.ANY;
			if ("+".equals(attr)) return Multiplicity.SOME;
			if ("1".equals(attr)) return Multiplicity.ONE;
			GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
					KExceptionGroup.COMPILER, 
					"Unknown multiplicity in configuration for cell " + this.getLabel() + ".", 
					this.getFilename(), this.getLocation()));
		}
		return Multiplicity.ONE;
	}
	
	public String getElipses() {
		return ellipses;
	}

	public void setElipses(String ellipses) {
		this.ellipses = ellipses;
		attributes.put("ellipses", ellipses);
	}

	public Map<String, String> getAttributes() {
		return attributes;
	}

	public void setAttributes(Map<String, String> attributes) {
		this.attributes = attributes;
	}

	public void setLabel(String label) {
		this.label = label;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		this.contents = (Term) visitor.modify(contents);
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
		attributes = new HashMap<String, String>();
	}
	
	@Override
	public Cell shallowCopy() {
		return new Cell(this);
	}
}
