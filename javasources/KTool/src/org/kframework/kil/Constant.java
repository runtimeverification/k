package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import java.util.HashMap;
import java.util.Map;


public class Constant extends Term {

    // AST representation of #Bool constants
    public static final Constant TRUE = new Constant("#Bool", "true");
    public static final Constant FALSE = new Constant("#Bool", "false");

    /*
     * AST representation of #Int, #String and KLabel constants; hashmaps cache
     * the constants to ensure uniqueness
     */
    private static final Map<Integer, Constant> ints
            = new HashMap<Integer, Constant>();
    public static final Constant ZERO = INT(0);
    public static final Constant ONE = INT(1);
    public static final Constant INT(int i) {
        Constant ct = ints.get(i);
        if (ct == null) {
            ct = new Constant("#Int", Integer.toString(i));
            ints.put(i, ct);
        }
        return ct;
    }

    private static final Map<String, Constant> strs
            = new HashMap<String, Constant>();
    public static final Constant SPACE = STRING(" ");
    public static final Constant STRING(String s) {
        Constant ct = strs.get(s);
        if (ct == null) {
            ct = new Constant("#String", "\"" + s + "\"");
            strs.put(s, ct);
        }
        return ct;
    }

    private static final Map<String, Constant> klbls
            = new HashMap<String, Constant>();
    public static final Constant KLABEL(String s) {
        Constant ct = klbls.get(s);
        if (ct == null) {
            ct = new Constant("KLabel", s);
            klbls.put(s, ct);
        }
        return ct;
    }


    protected final String value;

	public Constant(String sort, String value) {
		super(sort);
		this.value = value;
	}

	public Constant(String location, String filename, String sort, String value) {
		super(location, filename, sort);
		this.value = value;
	}

	public Constant(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.value = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public Constant(Constant constant) {
		super(constant);
		this.value = constant.value;
	}

    public String getValue() {
        return value;
    }

    @Override
	public String toString() {
		return value + " ";
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
	public Constant shallowCopy() {
		return new Constant(this);
	}
}
