package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/** A terminal in a {@link Production}. */
public class Lexical extends ProductionItem {

	private String lexicalRule;
	private String follow;

	public Lexical(String terminal, String follow) {
		super();
		this.lexicalRule = terminal;
		this.follow = follow;
	}

	public Lexical(Lexical terminal) {
		super(terminal);
		this.lexicalRule = terminal.lexicalRule;
		this.follow = terminal.follow;
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
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
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
