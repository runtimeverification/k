package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class LiterateDefinitionComment extends DefinitionItem implements LiterateComment {
	private String value;
	private LiterateCommentType lcType;

	public LiterateDefinitionComment(Element element) {
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

	public LiterateDefinitionComment(
			LiterateDefinitionComment literateDefinitionComment) {
		super(literateDefinitionComment);
		value = literateDefinitionComment.value;
		lcType = literateDefinitionComment.lcType; 
	}

	@Override
	public String toMaude() {
		return "";
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
}
