package org.kframework.parser.generator.basic;

public interface Item extends Cloneable {

	public enum ItemType {
		SORT, USERLIST, TERMINAL;
	}

	public Item clone();

	@Override
	public String toString();

	public ItemType getType();
}
