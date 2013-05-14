package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

/** A module or interface. */
public class Module extends DefinitionItem {
	private String name;
	private List<ModuleItem> items;
	/** "module" or "interface" */
	private String type;

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

	public List<String> getModuleKLabels() {
		List<String> mkl = new LinkedList<String>();

		for (ModuleItem mi : items) {
			List<String> list = mi.getKLabels();
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

        // Andrei S: bad, bad practice ...
        // ... but it is 11:55pm and I do not see another way to get them
        sorts.add("#Bool");
        sorts.add("#Int");
        sorts.add("#Float");
        sorts.add("#String");
        sorts.add("#Id");

		return sorts;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
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

	public void addSubsort(String sort, String subsort) {
		this.addProduction(sort, new Sort(subsort));
	}

	public void addConstant(String ctSort, String ctName) {
		this.addProduction(ctSort, new Terminal(ctName));
	}

    public void addConstant(Constant ct) {
        this.addProduction(ct.getSort(null), new Terminal(ct.getValue()));
    }

    public void addConstant(KLabelConstant kLabelConstant) {
        this.addProduction(kLabelConstant.getSort(null), new Terminal(kLabelConstant.getLabel()));
    }

	public void addProduction(String sort, ProductionItem prodItem) {
		List<ProductionItem> prodItems = new LinkedList<ProductionItem>();
		prodItems.add(prodItem);
		this.addProduction(sort, new Production(new Sort(sort), prodItems));
	}

	public void addProduction(String sort, Production prod) {
		List<PriorityBlock> pbs = new LinkedList<PriorityBlock>();
		PriorityBlock pb = new PriorityBlock();
		pbs.add(pb);

		List<Production> prods = new LinkedList<Production>();
		pb.setProductions(prods);

		prods.add(prod);

		this.items.add(new Syntax(new Sort(sort), pbs));
	}

    public List<Rule> getRules() {
        List<Rule> list = new LinkedList<Rule>();
        for (ModuleItem moduleItem : items) {
            if (moduleItem instanceof Rule) {
                list.add((Rule) moduleItem);
            }
        }

        return list;
    }
}
