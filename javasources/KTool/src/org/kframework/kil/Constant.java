package org.kframework.kil;

import java.util.HashMap;
import java.util.Map;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;


/** Atomic values in builtin sorts, including klabel.
 * All values are represented textually in {@link #value},
 * whose interpretation may depend on {@link #sort}.
 */
public class Constant extends Term {
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;
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

    public static final Constant INT(String s) {
        return new Constant("#Int", s);
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

	// AST representation of KLabel constants
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

	private Constant(String location, String filename, String sort, String value) {
		super(location, filename, sort);
		this.value = value;
	}

	public Constant(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.value = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	private Constant(Constant constant) {
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
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }


	@Override
	public Constant shallowCopy() {
		return new Constant(this);
	}

	@Override
	public boolean equals(Object o) {
		if (!(o instanceof Constant)) return false;
		Constant c = (Constant)o;
		return sort.equals(c.sort) && value.equals(c.value);
	}

	@Override
	public int hashCode() {
		return (sort + value).hashCode();
	}
}
