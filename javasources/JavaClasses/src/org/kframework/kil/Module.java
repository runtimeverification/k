package org.kframework.kil;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.utils.xml.XML;

public class Module extends DefinitionItem {
	private String name;
	private List<ModuleItem> items;
	private String type;
	private boolean predefined = false;

	public Module(Element element) {
		super(element);

		name = element.getAttribute(Constants.VALUE_value_ATTR);
		type = element.getAttribute(Constants.TYPE_type_ATTR);
		predefined = element.getAttribute(Constants.PREDEFINED).equals("true") ? true : false;
		items = new ArrayList<ModuleItem>();

		List<Element> elements = XML.getChildrenElements(element);
		for (Element e : elements) {
			ASTNode astn = JavaClassesFactory.getTerm(e);
			items.add((ModuleItem) astn);
		}
	}

	public Module(Module m) {
		super(m);
		this.name = m.name;
		this.type = m.type;
		this.predefined = m.predefined;
		this.items = m.items;
	}

	public Module() {
	}

	public Module(String name, String type, boolean predefined) {
		super();
		this.name = name;
		this.type = type;
		this.predefined = predefined;
	}

	public void appendModuleItem(ModuleItem item) {
		if (items == null)
			items = new LinkedList<ModuleItem>();
		this.items.add(item);
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setItems(List<ModuleItem> items) {
		this.items = items;
	}

	public List<ModuleItem> getItems() {
		return items;
	}

	public void setType(String type) {
		this.type = type;
	}

	public String getType() {
		return type;
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

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	public void setPredefined(boolean predefined) {
		this.predefined = predefined;
	}

	public boolean isPredefined() {
		return predefined;
	}

	public Module addModuleItems(List<ModuleItem> rules) {
		Module result = new Module(this);
		List<ModuleItem> items = new ArrayList<ModuleItem>(this.items);
		items.addAll(rules);
		result.setItems(items);
		return result;
	}

	@Override
	public Module shallowCopy() {
		return new Module(this);
	}
}
