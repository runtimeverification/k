package k3.basic;

import java.util.*;

import k.utils.Tag;
import k.utils.XmlLoader;

import org.w3c.dom.*;

public class Module extends ModuleItem implements Cloneable {
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
		setSentences(module);
	}

	private void setModuleName(Node module) {
		NamedNodeMap attr = module.getAttributes();
		moduleName = attr.getNamedItem(Tag.value).getNodeValue();
		type = attr.getNamedItem(Tag.type).getNodeValue();
		location = attr.getNamedItem(Tag.location).getNodeValue();
	}

	private void setSentences(Node module) {
		sentences = new ArrayList<Sentence>();

		// iterate through children
		Element element = (Element) module;
		NodeList children = element.getChildNodes();
		for (int i = 0; i < children.getLength(); i++) {
			if (children.item(i).getNodeName().equals(Tag.syntax)) {
				sentences.add(new Syntax(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.rule)) {
				sentences.add(new Rule(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.context)) {
				sentences.add(new Context(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.configuration)) {
				sentences.add(new Configuration(children.item(i)));
			} else if (children.item(i).getNodeName().equals(Tag.imports)) {
				Including incl = new Including(children.item(i));
				includes.add(incl.getIncludedModuleName());
				sentences.add(incl);
			}
		}
	}

	public void addComments(NodeList nl) {
		int loc0 = XmlLoader.getLocNumber(location, 0);
		int loc2 = XmlLoader.getLocNumber(location, 2);

		java.util.List<Sentence> comms = new ArrayList<Sentence>();
		java.util.List<Sentence> sents = sentences;
		for (int i = 0; i < nl.getLength(); i++) {
			Element el = (Element) nl.item(i);
			int eloc0 = XmlLoader.getLocNumber(el.getAttribute("loc"), 0);
			int eloc2 = XmlLoader.getLocNumber(el.getAttribute("loc"), 2);

			if (eloc0 >= loc0 && eloc2 <= loc2) {
				// comment inside my module
				comms.add(new Comment(el));
			}
		}

		// merging comments with sentences
		sentences = new ArrayList<Sentence>();
		int i = 0;
		int j = 0;

		while (i < sents.size() && j < comms.size()) {
			Sentence s = sents.get(i);
			Sentence com = comms.get(j);
			if (s.getStartLine() < com.getStartLine()) {
				sentences.add(s);
				i++;
			} else {
				sentences.add(com);
				j++;
			}
		}
		while (i < sents.size()) {
			sentences.add(sents.get(i));
			i++;
		}
		while (j < comms.size()) {
			sentences.add(comms.get(j));
			j++;
		}
		// fix the xmlNode
		Element el = (Element) xmlTerm;
		while (el.hasChildNodes())
			el.removeChild(el.getLastChild());
		Document doc = el.getOwnerDocument();
		for (Sentence s2 : sentences) {
			Element elm = (Element) doc.importNode(s2.xmlTerm, true);
			s2.xmlTerm = elm;
			el.appendChild(elm);
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

	public String getModuleType() {
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

	@Override
	public ModuleType getType() {
		return ModuleType.MODULE;
	}
}
