package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.List;

/**
 * An associativity declaration, one of {@code syntax left}, {@code syntax right}, or {@ code syntax non-assoc}.
 */
public class PriorityExtendedAssoc extends ModuleItem {
	/** "left", "right", "non-assoc" */
	String assoc = null;
	/** The labels getting an associativity. */
	java.util.List<Constant> tags;

	public String getAssoc() {
		return assoc;
	}

	public void setAssoc(String assoc) {
		this.assoc = assoc;
	}

	public java.util.List<Constant> getTags() {
		return tags;
	}

	public void setTags(java.util.List<Constant> tags) {
		this.tags = tags;
	}

	public PriorityExtendedAssoc(String assoc, java.util.List<Constant> tags) {
		super();
		this.tags = tags;
		this.assoc = assoc;
	}

	public PriorityExtendedAssoc(Element element) {
		super(element);

		this.assoc = element.getAttribute(Constants.ASSOC_assoc_ATTR);
		this.tags = new ArrayList<Constant>();
		List<Element> priorities = XML.getChildrenElementsByTagName(element, Constants.CONST);
		for (Element priority : priorities)
			tags.add((Constant) JavaClassesFactory.getTerm(priority));
	}

	public PriorityExtendedAssoc(PriorityExtendedAssoc node) {
		super(node);
		this.tags = node.tags;
	}

	@Override
	public String toString() {
		String blocks = "";

		for (Constant pb : tags) {
			blocks += pb + "\n> ";
		}
		if (blocks.length() > 2)
			blocks = blocks.substring(0, blocks.length() - 3);

		return "  syntax " + assoc + " " + blocks + "\n";
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
  public void accept(Matcher matcher, ASTNode toMatch){
    matcher.match(this, toMatch);
  }

	@Override
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (this == obj)
			return true;
		if (!(obj instanceof PriorityExtendedAssoc))
			return false;
		PriorityExtendedAssoc syn = (PriorityExtendedAssoc) obj;

		if (syn.tags.size() != tags.size())
			return false;

		for (int i = 0; i < syn.tags.size(); i++) {
			if (!syn.tags.get(i).equals(tags.get(i)))
				return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = assoc.hashCode();

		for (Constant pb : tags)
			hash += pb.hashCode();
		return hash;
	}

	@Override
	public PriorityExtendedAssoc shallowCopy() {
		return new PriorityExtendedAssoc(this);
	}
}
