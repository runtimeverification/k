package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Modifier;
import ro.uaic.info.fmse.parsing.Visitor;

public class LiterateDefinitionComment extends DefinitionItem implements LiterateComment {
	public LiterateDefinitionComment(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	@Override
	public String toMaude() {
		return "literate";
	}

	@Override
	public void applyToAll(Modifier visitor) {
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}
