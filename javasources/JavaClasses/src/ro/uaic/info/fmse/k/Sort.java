package ro.uaic.info.fmse.k;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.ASTNode;

public class Sort extends ASTNode implements ProductionItem{

	String sort;

	public Sort(Element element) {
		super(element);
		
		sort = element.getAttribute(Constants.VALUE);
	}
	
	@Override
	public String toString() {
		return sort;
	}
}
