package org.kframework.kil;

import org.kframework.kil.loader.AddConsesVisitor;
import org.kframework.kil.loader.CollectConfigCellsVisitor;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.CollectPrioritiesVisitor;
import org.kframework.kil.loader.CollectStartSymbolPgmVisitor;
import org.kframework.kil.loader.CollectSubsortsVisitor;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.UpdateAssocVisitor;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.DefinitionLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.xml.XML;

import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * Represents a language definition.
 * Includes contents from all {@code required}-d files.
 * @see DefinitionLoader
 * @see BasicParser
 */
public class Definition extends ASTNode {

	private java.util.List<DefinitionItem> items;
	private String mainFile;
	private String mainModule;
	/** An index of all modules in {@link #items} by name */
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
		// Collect information
		this.accept(new UpdateReferencesVisitor());
		this.accept(new AddConsesVisitor());
		this.accept(new CollectConsesVisitor());
		this.accept(new CollectSubsortsVisitor());
		this.accept(new CollectPrioritiesVisitor());
		this.accept(new CollectStartSymbolPgmVisitor());
		this.accept(new CollectConfigCellsVisitor());
		this.accept(new UpdateAssocVisitor());
		DefinitionHelper.initialized = true;
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
			if (i instanceof Module)
				modules.add((Module) i);
		}
		if (modules.size() != 1) {
			String msg = "Should have been only one module when calling this method.";
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, msg, this.getFilename(), this.getLocation()));
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
			String msg = "Should have been only one module when calling this method.";
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, msg, this.getFilename(), this.getLocation()));
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
