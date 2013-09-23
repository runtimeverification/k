package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * An associativity declaration, one of {@code syntax left}, {@code syntax right}, or {@ code syntax non-assoc}.
 */
public class PriorityExtendedAssoc extends ModuleItem {
	/** "left", "right", "non-assoc" */
	String assoc = null;
	/** The labels getting an associativity. */
	java.util.List<KLabelConstant> tags;

	public String getAssoc() {
		return assoc;
	}

	public void setAssoc(String assoc) {
		this.assoc = assoc;
	}

	public java.util.List<KLabelConstant> getTags() {
		return tags;
	}

	public void setTags(java.util.List<KLabelConstant> tags) {
		this.tags = tags;
	}

	public PriorityExtendedAssoc(String assoc, java.util.List<KLabelConstant> tags) {
		super();
		this.tags = tags;
		this.assoc = assoc;
	}

	public PriorityExtendedAssoc(PriorityExtendedAssoc node) {
		super(node);
		this.assoc = node.assoc;
		this.tags = node.tags;
	}

	@Override
	public String toString() {
		String blocks = "";

		for (KLabelConstant pb : tags) {
			blocks += pb + " ";
		}
		if (blocks.length() > 2)
			blocks = blocks.substring(0, blocks.length() - 1);

		return "  syntax " + assoc + " " + blocks + "\n";
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

		for (KLabelConstant pb : tags)
			hash += pb.hashCode();
		return hash;
	}

	@Override
	public PriorityExtendedAssoc shallowCopy() {
		return new PriorityExtendedAssoc(this);
	}
}
