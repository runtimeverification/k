package org.kframework.kil.visitors;

public interface Visitable {
	/**
	 * Implements a Visitor pattern.
	 * @param visitor
	 */
	public void accept(Visitor visitor);
}
