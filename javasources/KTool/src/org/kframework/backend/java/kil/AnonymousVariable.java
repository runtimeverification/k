package org.kframework.backend.java.kil;


/**
 * An anonymous variable. Anonymous variable names begin with the prefix "__var__".
 *
 * @author AndreiS
 */
public class AnonymousVariable extends Variable {

    private static final String VARIABLE_PREFIX = "__var__";
    private static int counter = 0;

    public static AnonymousVariable getFreshVariable(String sort) {
        return new AnonymousVariable(sort, counter++);
    }

	final private int id;

	private AnonymousVariable(String sort, int id) {
		super(VARIABLE_PREFIX + id, sort);
		this.id = id;
	}

	public int id() {
		return id;
	}

}
