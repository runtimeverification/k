package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.xml.XML;

public class Module extends DefinitionItem {
	String name;
	List<ModuleItem> items;
	String type;

	public Module(Element element) {
		super(element);

		name = element.getAttribute(Constants.VALUE_value_ATTR);
		type = element.getAttribute(Constants.TYPE_type_ATTR);
		items = new ArrayList<ModuleItem>();

		List<Element> elements = XML.getChildrenElements(element);
		for (Element e : elements) {
			items.add((ModuleItem) JavaClassesFactory.getTerm(e));
		}
	}

	@Override
	public String toString() {
		String content = "";
		for (ModuleItem i : items)
			content += i + " \n";

		return type + " " + name + "\n" + content + "\nend" + type;
	}

	@Override
	public String toMaude() {
		if (type.equals("interface")) return "";
		
		String content = "";
		for(ModuleItem mi : items)
			content += mi.toMaude() + "\n";
		
		return "mod " + name + " is\n" + content + "\nendm";
	}

	@Override
	public Element toXml(Document doc) {
		Element module = doc.createElement(Constants.MODULE);
		
		Element name = doc.createElement(Constants.NAME);
		name.setTextContent(this.name);
		module.appendChild(name);
		
		for(ModuleItem mi : items)
			module.appendChild(mi.toXml(doc));
				
		return module;
	}
}
