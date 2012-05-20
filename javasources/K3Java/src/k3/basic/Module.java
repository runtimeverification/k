package k3.basic;

import java.util.*;

import k.utils.Tag;
import org.w3c.dom.*;

public class Module extends Term implements Cloneable {
	// K statements
	private List<Sentence> sentences;
	private String moduleName;
	private Set<String> includes = new HashSet<String>();
	private String type = "";
	private boolean predefined = false;

	public Module clone() {
		Module m = new Module();
		m.copy(this);

		m.moduleName = moduleName;
		m.type = type;
		for (String incl : includes) {
			m.includes.add(incl);
		}

		for (Sentence s : sentences) {
			m.sentences.add(s.clone());
		}

		return m;
	}

	public Module() {
		sentences = new ArrayList<Sentence>();
		moduleName = "";
	}

	public List<Sentence> getSentences() {
		return sentences;
	}

	public void setSentences(List<Sentence> sentences) {
		this.sentences = sentences;
	}

	public Module(Node module, String filename) {
		this.filename = filename;
		this.xmlTerm = module;

		// set module name
		setModuleName(module);

		// set statements
		setSentences(module, filename);
	}

	private void setModuleName(Node module) {
		NamedNodeMap attr = module.getAttributes();
		moduleName = attr.getNamedItem(Tag.value).getNodeValue();
		type = attr.getNamedItem(Tag.type).getNodeValue();
		location = attr.getNamedItem(Tag.location).getNodeValue();
	}

	private void setSentences(Node module, String filename) {
		sentences = new ArrayList<Sentence>();

		// iterate through children
		Element element = (Element) module;
		NodeList children = element.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i).getNodeName().equals(Tag.syntax)) {
				sentences.add(new Syntax(children.item(i), filename));
			} else if (children.item(i).getNodeName().equals(Tag.rule)) {
				sentences.add(new Rule(children.item(i), filename));
			} else if (children.item(i).getNodeName().equals(Tag.context)) {
				sentences.add(new Context(children.item(i), filename));
			} else if (children.item(i).getNodeName().equals(Tag.configuration)) {
				sentences.add(new Configuration(children.item(i), filename));
			} else if (children.item(i).getNodeName().equals(Tag.imports)) {
				Including incl = new Including(children.item(i));
				includes.add(incl.getIncludedModuleName());
				sentences.add(incl);
			}
		}
	}

	public String getModuleName() {
		return moduleName;
	}

	public void setModuleName(String moduleName) {
		this.moduleName = moduleName;
	}

	public void setType(String type) {
		this.type = type;
	}

	public String getType() {
		return type;
	}

	public void setPredefined(boolean predefined) {
		this.predefined = predefined;
		Element elm = (Element) this.xmlTerm;
		elm.setAttribute("predefined", predefined + "");
	}

	public boolean isPredefined() {
		return predefined;
	}
}
