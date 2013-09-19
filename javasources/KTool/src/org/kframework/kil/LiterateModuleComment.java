package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class LiterateModuleComment extends ModuleItem implements LiterateComment {

	private String value;
	private LiterateCommentType lcType;

	public LiterateModuleComment(LiterateModuleComment literateModuleComment) {
		super(literateModuleComment);
		value = literateModuleComment.value;
		lcType = literateModuleComment.lcType;
	}

	public LiterateModuleComment(String value, LiterateCommentType lcType) {
		this.value = value;
		this.lcType = lcType;
	}

	public LiterateModuleComment(LiterateDefinitionComment ldc) {
		setFilename(ldc.getFilename());
		setLocation(ldc.getLocation());
		value = ldc.getValue();
		lcType = ldc.getType();
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
	public LiterateCommentType getType() {
		return lcType;
	}

	public void setValue(String value) {
		this.value = value;
	}

	public String getValue() {
		return value;
	}

	@Override
	public LiterateModuleComment shallowCopy() {
		return new LiterateModuleComment(this);
	}

	@Override
	public String toString() {
		return "/*"+lcType+value+"*/";
	}
}
