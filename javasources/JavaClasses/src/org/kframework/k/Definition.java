package org.kframework.k;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.kframework.exceptions.TransformerException;
import org.kframework.loader.CollectConsesVisitor;
import org.kframework.loader.CollectListConsesVisitor;
import org.kframework.loader.Constants;
import org.kframework.loader.JavaClassesFactory;
import org.kframework.visitors.Modifier;
import org.kframework.visitors.Transformer;
import org.kframework.visitors.Visitor;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.utils.xml.XML;

public class Definition extends ASTNode {

	private java.util.List<DefinitionItem> items;
	private String mainFile;
	private String mainModule;
	private Map<String, Module> modulesMap;
	private String mainSyntaxModule;

	public Definition() {
		super("File System", "generated");
	}

	public Definition(Definition d) {
		super(d);
		this.mainFile = d.mainFile;
		this.mainModule = d.mainModule;
		this.mainSyntaxModule = d.mainSyntaxModule;
		this.items = d.items;
	}

	public Definition(Element element) {
		super(element);

		mainFile = element.getAttribute(Constants.MAINFILE);
		mainModule = element.getAttribute(Constants.MAINMODULE);
		// mainSyntaxModule = element.getAttribute(Constants.MAINSYNTAXMODULE);
		items = new ArrayList<DefinitionItem>();

		List<Element> elements = XML.getChildrenElements(element);
		for (Element e : elements)
			items.add((DefinitionItem) JavaClassesFactory.getTerm(e));
	}

	public void appendDefinitionItem(DefinitionItem di) {
		items.add(di);
	}

	public void appendBeforeDefinitionItem(DefinitionItem di) {
		items.add(0, di);
	}

	@Override
	public String toString() {
		String content = "";
		for (DefinitionItem di : items)
			content += di + " \n";

		return "DEF: " + mainFile + " -> " + mainModule + "\n" + content;
	}

	@Override
	public String toMaude() {
		String content = "";

		for (DefinitionItem di : items) {
			content += di.toMaude() + " \n";
		}

		return content;
	}


	@Override
	public Element toXml(Document doc) {

		// create <definition> element, together with attributes
		Element definition = doc.createElement(Constants.DEFINITION);
		definition.setAttribute(Constants.MAINFILE, mainFile);
		definition.setAttribute(Constants.MAINMODULE, mainModule);
		definition.setAttribute(Constants.MAINSYNTAXMODULE, mainSyntaxModule);

		// collect all the other items
		for (DefinitionItem di : items) {
			definition.appendChild(di.toXml(doc));
		}

		return definition;
	}

	@Override
	public void applyToAll(Modifier visitor) {
		for (int i = 0; i < this.items.size(); i++) {
			DefinitionItem di = (DefinitionItem) visitor.modify(this.items
					.get(i));
			this.items.set(i, di);
		}
	}

	public void setItems(List<DefinitionItem> items) {
		this.items = items;
	}

	public List<DefinitionItem> getItems() {
		return items;
	}

	public void setMainFile(String mainFile) {
		this.mainFile = mainFile;
	}

	public String getMainFile() {
		return mainFile;
	}

	public void setMainModule(String mainModule) {
		this.mainModule = mainModule;
	}

	public String getMainModule() {
		return mainModule;
	}

	public void setMainSyntaxModule(String mainSyntaxModule) {
		this.mainSyntaxModule = mainSyntaxModule;
	}

	public String getMainSyntaxModule() {
		return mainSyntaxModule;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

	public void preprocess() {
		// Collect conses
		this.accept(new CollectConsesVisitor());
		this.accept(new CollectListConsesVisitor());
	}

	public Map<String, Module> getModulesMap() {
		return modulesMap;
	}

	public void setModulesMap(Map<String, Module> modulesMap) {
		this.modulesMap = modulesMap;
	}
	
	
	public Module getSingletonModule() {
		List<Module> modules = new LinkedList<Module>();
		for (DefinitionItem i : this.getItems()) {
			if (i instanceof Module) modules.add((Module)i);
		}
		if (modules.size() != 1) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Should have been only one module when calling this method.", 
					this.getFilename(), this.getLocation(), 0));			
		}
		return modules.get(0);
	}

	public Definition updateSingletonModule(Module mod) {
		int moduleCount = 0;
		List<DefinitionItem> newDefinitionItems = new ArrayList<DefinitionItem>();
		for (DefinitionItem i : this.getItems()) {
			if (i instanceof Module) {
				moduleCount++;
				newDefinitionItems.add(mod);
			} else {
				newDefinitionItems.add(i);
			}
		}
		if (moduleCount != 1) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Should have been only one module when calling this method.", 
					this.getFilename(), this.getLocation(), 0));			
		}
		Definition result = new Definition(this);
		result.setItems(newDefinitionItems);
		return result;
	}
	
	@Override
	public Definition shallowCopy() {
		return new Definition(this);
	}
}
