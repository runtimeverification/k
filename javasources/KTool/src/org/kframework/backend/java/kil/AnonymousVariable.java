package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Utils;


/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/8/13 Time: 3:08 PM To change this template use File | Settings | File Templates.
 */
public class AnonymousVariable extends Variable {

    public static final String VARIABLE_PREFIX = "__var__";

    static private int counter = 0;

	final private int id;

	private AnonymousVariable(String sort, int id) {
		super(VARIABLE_PREFIX + id, sort);
		this.id = id;
	}

	public static AnonymousVariable getFreshVariable(String sort) {
		return new AnonymousVariable(sort, counter++);
	}

	public int getId() {
		return id;
	}

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof AnonymousVariable)) {
            return false;
        }
        AnonymousVariable anonymousVariable = (AnonymousVariable) object;
        return id == anonymousVariable.id && super.equals(anonymousVariable);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + id;
        hash = hash * Utils.HASH_PRIME + sort.hashCode();
        return hash;
    }

}
