package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/** A subclass of {@link Empty} used to represent both typed and untyped cons list terminators.
 * Distinguished by {@link #sort} and {@link #separator} */
public class ListTerminator extends Empty {

	private String separator;

	public ListTerminator(String sort, String separator) {
		super(sort);
		this.separator = separator;
	}

	public ListTerminator(String separator) {
		super("K");
		this.separator = separator;
	}

	public ListTerminator(ListTerminator terminator) {
		super(terminator);
		this.separator = separator;
	}

	public String toString() {
		if (sort.equals("K"))
			return ".List{\"" + separator + "\"} ";
		else
			return super.toString();
	}

	public String getSeparator() {
		return separator;
	}

	public void setSeparator(String separator) {
		this.separator = separator;
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
	public ListTerminator shallowCopy() {
		return new ListTerminator(this);
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof ListTerminator)) return false;
		ListTerminator l = (ListTerminator)o;
		return sort.equals(l.sort) && separator.equals(l.separator);
	}

	@Override
	public int hashCode() {
		return (sort + separator).hashCode();
	}
}
