package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.CollectConsesVisitor;
import ro.uaic.info.fmse.loader.CollectListConsesVisitor;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.transitions.maude.CellLabelsVisitor;
import ro.uaic.info.fmse.transitions.maude.KLabelsVisitor;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.visitors.Modifier;
import ro.uaic.info.fmse.visitors.Transformer;
import ro.uaic.info.fmse.visitors.Visitor;

public class Definition extends ASTNode {

	private java.util.List<DefinitionItem> items;
	private String mainFile;
	private String mainModule;
	private String mainSyntaxModule;

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

		String uris = "";
		for (DefinitionItem di : items) {
			// if (di instanceof Module && ((Module)di).name.equals("URIS"))
			// uris = di.toMaude();
			// else
			content += di.toMaude() + " \n";
		}

		// klabels
		String klabels = "";
		KLabelsVisitor labelsVisitor = new KLabelsVisitor();
		accept(labelsVisitor);
		for (String kl : labelsVisitor.kLabels) {
			klabels += kl + " ";
		}
		klabels = klabels.trim();
		if (!klabels.equals(""))
			klabels = "  ops " + klabels + " : -> KLabel .\n";

		// cellLabels visitor
		String cellLabels = "";
		CellLabelsVisitor cellLabelsVisitor = new CellLabelsVisitor();
		accept(cellLabelsVisitor);
		for (String cellLabel : cellLabelsVisitor.cellLabels) {
			cellLabels += cellLabel + " ";
		}
		cellLabels = cellLabels.trim();
		if (!cellLabels.equals(""))
			cellLabels = "  ops " + cellLabels + " : -> CellLabel .\n";

		// sorts & automatic subsortation to K
		String sorts = "";
		for (String s : MaudeHelper.declaredSorts) {
			if (!MaudeHelper.basicSorts.contains(s) && !s.startsWith("#"))
				sorts += s + " ";
		}
		sorts = sorts.trim();
		if (!sorts.equals(""))
			sorts = "  sorts " + sorts + " .\n  subsorts " + sorts + " < K .\n";

		String shared = "mod " + Constants.SHARED + " is\n  including K .\n" + klabels + sorts + cellLabels + "\nendm";

		return uris + "\n" + shared + "\n" + content;
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
			DefinitionItem di = (DefinitionItem) visitor.modify(this.items.get(i));
			this.items.set(i, di);
		}
	}

	public void setItems(java.util.List<DefinitionItem> items) {
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
	public ASTNode accept(Transformer visitor) {
		return visitor.transform(this);
	}

	public void preprocess() {
		// Collect conses
		this.accept(new CollectConsesVisitor());
		this.accept(new CollectListConsesVisitor());
	}
}
