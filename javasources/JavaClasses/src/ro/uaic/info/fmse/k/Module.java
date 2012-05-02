package ro.uaic.info.fmse.k;

import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;

public class Module extends DefinitionItem {
	String name;
	List<ModuleItem> items;

	public Module(Element element) {
		super(element);
		
		name = element.getAttribute(Constants.VALUE_value_ATTR);
		items = new LinkedList<ModuleItem>();

		List<Element> elements = XML.getChildrenElements(element);
		for(Element e : elements)
		{
			items.add((ModuleItem)JavaClassesFactory.getTerm(e));
		}
	}
	
	@Override
	public String toString() {
		String content = "";
		for (ModuleItem i : items)
			content += i + " \n";

		return "module " + name + "\n" + content + "\nendmodule";
	}
}
