package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class LiterateDefinitionComment extends DefinitionItem implements LiterateComment {
	private String value;
	private LiterateCommentType lcType = LiterateCommentType.COMMON;

	public LiterateDefinitionComment(String value, LiterateCommentType lcType) {
		this.value = value;
		this.lcType = lcType;
	}

	public LiterateDefinitionComment(LiterateDefinitionComment literateDefinitionComment) {
		super(literateDefinitionComment);
		value = literateDefinitionComment.value;
		lcType = literateDefinitionComment.lcType;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	public void setValue(String value) {
		this.value = value;
	}

	public String getValue() {
		return value;
	}

	@Override
	public LiterateCommentType getType() {
		return lcType;
	}

	@Override
	public LiterateDefinitionComment shallowCopy() {
		return new LiterateDefinitionComment(this);
	}

	@Override
	public String toString() {
		return "/*"+lcType+value+"*/";
	}
}
