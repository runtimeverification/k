package ro.uaic.info.fmse.k;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.parsing.Visitor;

public class LiterateModuleComment extends ModuleItem implements
		LiterateComment {

	public LiterateModuleComment(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}

	@Override
	public String toMaude() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Element toXml(Document doc) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}
