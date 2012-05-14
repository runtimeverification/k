package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;
import ro.uaic.info.fmse.transitions.maude.CellLabelsVisitor;
import ro.uaic.info.fmse.transitions.maude.KLabelsVisitor;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;
import ro.uaic.info.fmse.utils.xml.XML;

public class Definition extends ASTNode {

	java.util.List<DefinitionItem> items;
	String mainFile;
	String mainModule;
	String mainSyntaxModule;

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

		for (DefinitionItem di : items)
			content += di.toMaude() + "\n";

		// klabels
		String klabels = "";
		KLabelsVisitor labelsVisitor = new KLabelsVisitor();
		this.accept(labelsVisitor);
		for (String kl : labelsVisitor.kLabels) {
			klabels += kl + " ";
		}
		klabels = klabels.trim();
		if (!klabels.equals(""))
			klabels = "  ops " + klabels + " : -> KLabel .\n";

		// cellLabels visitor
		String cellLabels = "";
		CellLabelsVisitor cellLabelsVisitor = new CellLabelsVisitor();
		this.accept(cellLabelsVisitor);
		for (String cellLabel : cellLabelsVisitor.cellLabels) {
			cellLabels += cellLabel + " ";
		}
		cellLabels = cellLabels.trim();
		if (!cellLabels.equals(""))
			cellLabels = "  ops " + cellLabels + " : -> CellLabel .\n";

		// sorts & automatic subsortation to K
		String sorts = "";
		for (String s : MaudeHelper.declaredSorts)
			if (!MaudeHelper.basicSorts.contains(s))
				sorts += s + " ";
		sorts = sorts.trim();
		if (!sorts.equals(""))
			sorts = "  sorts " + sorts + " .\n  subsorts " + sorts + " < K .\n";

		return "mod " + Constants.SHARED + " is\n  including K + URIS .\n" + klabels + sorts + cellLabels + "\nendm\n" + content;
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
	public void accept(Visitor visitor) {
		visitor.visit(this);
		for (DefinitionItem di : items)
			di.accept(visitor);
	}

	@Override
	public void all(Visitor visitor) {
		for (int i = 0; i < this.items.size(); i++) {
			DefinitionItem di = (DefinitionItem) visitor.visit(this.items.get(i));
			this.items.set(i, di);
		}
	}
}
