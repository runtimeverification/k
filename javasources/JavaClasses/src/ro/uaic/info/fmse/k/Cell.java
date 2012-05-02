package ro.uaic.info.fmse.k;

import java.util.Map;

import org.w3c.dom.Element;

public class Cell extends Term {
	public Cell(Element element) {
		super(element);
		// TODO Auto-generated constructor stub
	}
	Term label;
	Term contents;
	String sort;
	Map<String, Object> attributes;

}
