package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.List;

public class PriorityExtended extends ModuleItem {
	java.util.List<PriorityBlockExtended> priorityBlocks;

	public PriorityExtended(Sort sort, java.util.List<PriorityBlockExtended> priorities) {
		super();
		this.priorityBlocks = priorities;
	}

	public java.util.List<PriorityBlockExtended> getPriorityBlocks() {
		return priorityBlocks;
	}

	public void setPriorityBlocks(java.util.List<PriorityBlockExtended> priorityBlocks) {
		this.priorityBlocks = priorityBlocks;
	}

	public PriorityExtended(Element element) {
		super(element);

		// assumption: sorts contains only one element
		this.priorityBlocks = new ArrayList<PriorityBlockExtended>();
		List<Element> priorities = XML.getChildrenElementsByTagName(element, Constants.PRIBLOCK);
		for (Element priority : priorities)
			priorityBlocks.add((PriorityBlockExtended) JavaClassesFactory.getTerm(priority));
	}

	public PriorityExtended(PriorityExtended node) {
		super(node);
		this.priorityBlocks = node.priorityBlocks;
	}

	@Override
	public String toString() {
		String blocks = "";

		for (PriorityBlockExtended pb : priorityBlocks) {
			blocks += pb + "\n> ";
		}
		if (blocks.length() > 2)
			blocks = blocks.substring(0, blocks.length() - 3);

		return "  syntax priorities" + blocks + "\n";
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
		if (this == obj)
			return true;
		if (!(obj instanceof PriorityExtended))
			return false;
		PriorityExtended syn = (PriorityExtended) obj;

		if (syn.priorityBlocks.size() != priorityBlocks.size())
			return false;

		for (int i = 0; i < syn.priorityBlocks.size(); i++) {
			if (!syn.priorityBlocks.get(i).equals(priorityBlocks.get(i)))
				return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = 0;

		for (PriorityBlockExtended pb : priorityBlocks)
			hash += pb.hashCode();
		return hash;
	}

	@Override
	public PriorityExtended shallowCopy() {
		return new PriorityExtended(this);
	}
}
