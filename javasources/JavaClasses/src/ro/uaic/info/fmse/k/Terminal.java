package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

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

	public Terminal(Terminal terminal2) {
		super(terminal2);
		terminal = terminal2.terminal;
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
		return "\"" + terminal + "\"";
	}

	@Override
	public String toMaude() {
		return "";
	}

	@Override
	public Element toXml(Document doc) {
		Element terminal = doc.createElement(Constants.TERMINAL);
		terminal.setTextContent(this.terminal);
		return terminal;
	}

	public void accept(Modifier visitor) {
		visitor.modify(this);
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
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

		if (trm.getTerminal().equals(this.terminal))
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
