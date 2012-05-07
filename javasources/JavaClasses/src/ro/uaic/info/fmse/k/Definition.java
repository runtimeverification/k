package ro.uaic.info.fmse.k;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
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
		for(DefinitionItem di : items)
		{
			definition.appendChild(di.toXml(doc));
		}
		
		return definition;
	}
}
