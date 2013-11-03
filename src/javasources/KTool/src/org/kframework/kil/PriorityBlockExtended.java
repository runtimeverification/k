package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;

/** A group within a {@code syntax priorities} declaration.
 * @see PriorityExtended */
public class PriorityBlockExtended extends ASTNode {

	java.util.List<KLabelConstant> productions = new ArrayList<KLabelConstant>();

	public java.util.List<KLabelConstant> getProductions() {
		return productions;
	}

	public void setProductions(java.util.List<KLabelConstant> productions) {
		this.productions = productions;
	}

	public PriorityBlockExtended() {
		super();
	}

	public PriorityBlockExtended(PriorityBlockExtended node) {
		super(node);
		this.productions.addAll(node.productions);
	}

	public PriorityBlockExtended(java.util.List<KLabelConstant> productions) {
		super();
		this.productions.addAll(productions);
	}

	@Override
	public String toString() {
		String content = "";
		for (Term production : productions)
			content += production + " ";

		if (content.length() > 2)
			content = content.substring(0, content.length() - 1);

		return content;
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
		if (!(obj instanceof PriorityBlockExtended))
			return false;
		PriorityBlockExtended pb = (PriorityBlockExtended) obj;

		if (pb.productions.size() != productions.size())
			return false;

		for (int i = 0; i < pb.productions.size(); i++) {
			if (!pb.productions.get(i).equals(productions.get(i)))
				return false;
		}

		return true;
	}

	@Override
	public int hashCode() {
		int hash = 0;

		for (Term prd : productions)
			hash += prd.hashCode();
		return hash;
	}

	@Override
	public PriorityBlockExtended shallowCopy() {
		return new PriorityBlockExtended(this);
	}
}
