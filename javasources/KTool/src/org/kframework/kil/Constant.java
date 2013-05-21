package org.kframework.kil;

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
@Deprecated
public class Constant extends Term {
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;

    protected final String value;

	public Constant(String sort, String value) {
		super(sort);

		this.value = value;

        assert !(sort.equals(KSorts.KLABEL) || sort.equals("#Bool") || sort.equals("#Int")
                || sort.equals("#Float") || sort.equals("#String"));
	}

	public Constant(Element element) {
		super(element);
		this.sort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.value = element.getAttribute(Constants.VALUE_value_ATTR);

        assert !(sort.equals(KSorts.KLABEL) || sort.equals("#Bool") || sort.equals("#Int")
                || sort.equals("#Float") || sort.equals("#String"));
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
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
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
