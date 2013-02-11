package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

/** A terminal in a {@link Production}. */
public class Lexical extends ProductionItem {

	private String lexicalRule;
	private String follow;

	public Lexical(Element element) {
		super(element);
		lexicalRule = StringUtil.unescape(element.getAttribute(Constants.VALUE_value_ATTR));
		if (element.hasAttribute("follow"))
			follow = StringUtil.unescape(element.getAttribute("follow"));
	}

	public Lexical(String terminal) {
		super();
		this.lexicalRule = terminal;
	}

	public Lexical(Lexical terminal) {
		super(terminal);
		this.lexicalRule = terminal.lexicalRule;
		this.follow = terminal.follow;
	}

	public ProductionType getType() {
		return ProductionType.LEXICAL;
	}

	@Override
	public String toString() {
		return "Lexical{" + lexicalRule + "}";
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
	public boolean equals(Object obj) {
		if (obj == null)
			return false;
		if (obj == this)
			return true;
		if (!(obj instanceof Lexical))
			return false;

		Lexical trm = (Lexical) obj;

		if (!trm.lexicalRule.equals(this.lexicalRule))
			return false;
		return true;
	}

	@Override
	public int hashCode() {
		return this.lexicalRule.hashCode();
	}

	@Override
	public Lexical shallowCopy() {
		return new Lexical(this);
	}

	public void setFollow(String follow) {
		this.follow = follow;
	}

	public String getFollow() {
		return follow;
	}

	public String getLexicalRule() {
		return lexicalRule;
	}

	public void setLexicalRule(String lexicalRule) {
		this.lexicalRule = lexicalRule;
	}
}
