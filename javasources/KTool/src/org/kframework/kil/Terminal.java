package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

/** A terminal in a {@link Production}. */
public class Terminal extends ProductionItem {

	private String terminal;

	public Terminal(Element element) {
		super(element);
		terminal = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	public Terminal(String terminal) {
		super();
		this.terminal = terminal;
	}

	public Terminal(Terminal terminal) {
		super(terminal);
		this.terminal = terminal.terminal;
	}

	public void setTerminal(String terminal) {
		this.terminal = terminal;
	}

	public String getTerminal() {
		return terminal;
	}

	public ProductionType getType() {
		return ProductionType.TERMINAL;
	}

	@Override
	public String toString() {
		return "\"" + StringUtil.escape(terminal) + "\"";
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
		if (obj == this)
			return true;
		if (!(obj instanceof Terminal))
			return false;

		Terminal trm = (Terminal) obj;

		if (!trm.terminal.equals(this.terminal))
			return false;
		return true;
	}

	@Override
	public int hashCode() {
		return this.terminal.hashCode();
	}

	@Override
	public Terminal shallowCopy() {
		return new Terminal(this);
	}
}
