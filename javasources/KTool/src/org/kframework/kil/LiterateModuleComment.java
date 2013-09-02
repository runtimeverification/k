package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

public class LiterateModuleComment extends ModuleItem implements LiterateComment {

	private String value;
	private LiterateCommentType lcType;

	public LiterateModuleComment(Element element) {
		super(element);
		setValue(element.getAttribute(Constants.VALUE_value_ATTR));
		if (element.hasAttribute("special")) {
			String special = element.getAttribute("special");
			if (special.equals("latex"))
				this.lcType = LiterateCommentType.LATEX;
			else if (special.equals("preamble"))
				this.lcType = LiterateCommentType.PREAMBLE;
		} else
			this.lcType = LiterateCommentType.COMMON;
	}

	public LiterateModuleComment(LiterateModuleComment literateModuleComment) {
		super(literateModuleComment);
		value = literateModuleComment.value;
		lcType = literateModuleComment.lcType;
	}

	public LiterateModuleComment(String value) {
		this.value = value;
		this.lcType = LiterateCommentType.COMMON;
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
		return "/*"+value+"*/";
	}
}
