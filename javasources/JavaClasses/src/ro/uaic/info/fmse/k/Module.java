package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.Modifier;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.utils.xml.XML;

public class Module extends DefinitionItem {
	private String name;
	List<ModuleItem> items;
	String type;
	boolean predefined = false;

	public Module(Element element) {
		super(element);

		name = element.getAttribute(Constants.VALUE_value_ATTR);
		type = element.getAttribute(Constants.TYPE_type_ATTR);
		predefined = element.getAttribute(Constants.PREDEFINED).equals("true") ? true : false;
		items = new ArrayList<ModuleItem>();

		List<Element> elements = XML.getChildrenElements(element);
		for (Element e : elements) {
			items.add((ModuleItem) JavaClassesFactory.getTerm(e));
		}
	}
	
	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public List<ModuleItem> getItems() {
		return items;
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
		if (type.equals("interface"))
			return "";

		String content = "";

		items.add(0, new Import(Constants.SHARED));
		if (!predefined)
			items.add(0, new Import("URIS"));

		for (ModuleItem mi : items) {
			content += mi.toMaude() + "\n";
		}

		return "mod " + name + " is\n" + content + "\nendm";
	}

	public List<String> getModuleKLabels() {
		List<String> mkl = new LinkedList<String>();

		for (ModuleItem mi : items) {
			List<String> list = mi.getLabels();
			if (list != null)
				mkl.addAll(list);
		}

		return mkl;
	}

	public java.util.Set<String> getAllSorts() {
		java.util.Set<String> sorts = new HashSet<String>();

		for (ModuleItem mi : items) {
			List<String> list = mi.getAllSorts();
			if (list != null)
				sorts.addAll(list);
		}

		return sorts;
	}
		
	@Override
	public Element toXml(Document doc) {
		Element module = doc.createElement(Constants.MODULE);

		Element name = doc.createElement(Constants.NAME);
		name.setTextContent(this.name);
		module.appendChild(name);

		for (ModuleItem mi : items)
			module.appendChild(mi.toXml(doc));

		return module;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.items.size(); i++) {
			ModuleItem elem = (ModuleItem) visitor.modify(this.items.get(i));
			this.items.set(i, elem);
		}
	}
	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}
