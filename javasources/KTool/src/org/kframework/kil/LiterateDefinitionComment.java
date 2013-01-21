package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

public class LiterateDefinitionComment extends DefinitionItem implements LiterateComment {
	private String value;
	private LiterateCommentType lcType = LiterateCommentType.COMMON;

	public LiterateDefinitionComment(Element element) {
		super(element);
		setValue(StringUtil.unescape(element.getAttribute(Constants.VALUE_value_ATTR)));

		if (value.startsWith("//"))
			value = value.substring(2, value.length() - 1); // remove // and \n from beginning and end
		else
			value = value.substring(2, value.length() - 2); // remove /* and */ from beginning and end

		if (value.startsWith("@")) {
			lcType = LiterateCommentType.LATEX;
			value = value.substring(1);
		}
		if (value.startsWith("!")) {
			lcType = LiterateCommentType.PREAMBLE;
			value = value.substring(1);
		}
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
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

  @Override
  public void accept(Matcher matcher, ASTNode toMatch){
    matcher.match(this, toMatch);
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
		String shortStr = value;
		if (value.indexOf("\n") > 0)
			value.substring(0, value.indexOf("\n") - 1);
		return shortStr;
	}
}
