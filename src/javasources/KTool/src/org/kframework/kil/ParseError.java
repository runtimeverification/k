package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import aterm.ATermAppl;
import aterm.ATermInt;
import aterm.ATermList;

/**
 * Applications that are not in sort K, or have not yet been flattened.
 */
public class ParseError extends ASTNode {
	/** A unique identifier corresponding to a production, matching the SDF cons */
	String message = null;

	public ParseError(ATermAppl atm) {
		super("temp", "temp");
		this.message = ((ATermAppl) atm.getArgument(0)).getName() + ": ";

		ATermList list = (ATermList) atm.getArgument(1);
		atm = (ATermAppl) list.getFirst();
		this.message += ((ATermAppl) atm.getArgument(0)).getName();
		atm = (ATermAppl) atm.getArgument(1);
		String filename = ((ATermAppl) atm.getChildAt(0)).getName();
		atm = (ATermAppl) atm.getArgument(1);
		int loc0 = ((ATermInt) atm.getChildAt(0)).getInt();
		int loc1 = ((ATermInt) atm.getChildAt(1)).getInt();
		int loc2 = ((ATermInt) atm.getChildAt(2)).getInt();
		int loc3 = ((ATermInt) atm.getChildAt(3)).getInt();
		String loc = "(" + loc0 + "," + loc1 + "," + loc2 + "," + loc3 + ")";
		this.setLocation(loc);
		this.setFilename(filename);
	}

	public ParseError(ParseError node) {
		super(node);
		this.message = node.message;
	}

	@Override
	public String toString() {
		return "Parse error: " + message;
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
		if (!(obj instanceof ParseError))
			return false;
		ParseError tc = (ParseError) obj;

		return tc.message.equals(this.message);
	}

	@Override
	public int hashCode() {
		return message.hashCode();
	}

	@Override
	public ParseError shallowCopy() {
		return new ParseError(this);
	}

	public String getMessage() {
		return message;
	}

	public void setMessage(String message) {
		this.message = message;
	}
}
