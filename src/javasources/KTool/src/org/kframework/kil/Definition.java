package org.kframework.kil;

import org.kframework.compile.sharing.DataStructureSortCollector;
import org.kframework.compile.sharing.TokenSortCollector;
import org.kframework.kil.loader.*;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.DefinitionLoader;
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
import java.util.Set;


/**
 * Represents a language definition.
 * Includes contents from all {@code required}-d files.
 * @see DefinitionLoader
 * @see BasicParser
 */
public class Definition extends ASTNode {

	private List<DefinitionItem> items;
	private String mainFile;
	private String mainModule;
	/** An index of all modules in {@link #items} by name */
	private Map<String, Module> modulesMap;
	private String mainSyntaxModule;

	public Definition() {
		super();
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
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	public void preprocess(org.kframework.kil.loader.Context context) {
		// Collect information
		this.accept(new UpdateReferencesVisitor(context));
		this.accept(new AddConsesVisitor(context));
		this.accept(new CollectConsesVisitor(context));
		this.accept(new CollectSubsortsVisitor(context));
		this.accept(new CollectPrioritiesVisitor(context));
		this.accept(new CollectStartSymbolPgmVisitor(context));
		this.accept(new CollectConfigCellsVisitor(context));
		this.accept(new UpdateAssocVisitor(context));
		this.accept(new CollectLocationsVisitor(context));
        this.accept(new CountNodesVisitor(context));

        /* collect lexical token sorts */
        TokenSortCollector tokenSortCollector = new TokenSortCollector(context);
        this.accept(tokenSortCollector);
        // TODO(AndreiS): remove from K #Id
        Set<String> tokenSorts = tokenSortCollector.getSorts();
        tokenSorts.add("#Id");
        context.setTokenSorts(tokenSorts);

        /* collect the data structure sorts */
        DataStructureSortCollector dataStructureSortCollector
                = new DataStructureSortCollector(context);
        this.accept(dataStructureSortCollector);
        context.setDataStructureSorts(dataStructureSortCollector.getSorts());

        /* set the initialized flag */
        context.initialized = true;
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

	public Configuration getSingletonConfiguration() throws ConfigurationNotUnique, ConfigurationNotFound {
		Configuration result = null;
		for (DefinitionItem i : this.getItems()) {
			if (i instanceof Module) {
				if (((Module)i).isPredefined()) {
					continue;
				}
				for (ModuleItem j : ((Module) i).getItems()) {
					if (j instanceof Configuration) {
						if (result != null) {
							throw new ConfigurationNotUnique();
						} else {
							result = (Configuration)j;
						}
					}
				}
			}
		}
		if (result == null) {
			throw new ConfigurationNotFound();
		}
		return result;
	}
}
