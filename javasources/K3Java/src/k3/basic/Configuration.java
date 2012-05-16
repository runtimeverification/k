package k3.basic;

import java.util.*;

import k.utils.Error;
import k.utils.StringUtil;
import k.utils.Tag;
import k.utils.XmlLoader;

import org.w3c.dom.*;

public class Configuration extends Sentence {
	private static final long serialVersionUID = 1L;
	private String content;
	private boolean parsed = false;
	private Map<String, Cell> cellLabels;

	public Configuration clone() {
		// super.clone();
		// Configuration c = new Configuration();
		// c.copy(this);
		// c.content = content;
		// c.parsed = parsed;
		// for (Map.Entry<String, Cell> e : cellLabels.entrySet()) {
		// c.cellLabels.put(e.getKey(), e.getValue());
		// }
		// not sure if I'm modifying this anywhere

		return this;
	}

	public Configuration() {
		content = "";
		cellLabels = new HashMap<String, Cell>();
	}

	public Configuration(Node node, String filename) {
		this.filename = filename;
		this.xmlTerm = node;

		NamedNodeMap attr = node.getAttributes();
		Node item = attr.getNamedItem(Tag.location);
		location = item.getNodeValue();

		item = attr.getNamedItem(Tag.value);
		setContent(StringUtil.unescape(item.getNodeValue()));
	}

	public void parse() {
		cellLabels = new HashMap<String, Cell>();

		try {
			String parsed = k3parser.KParser.ParseKConfigString(content);
			Document doc = XmlLoader.getXMLDoc(parsed);

			// replace the old xml node with the newly parsed sentence
			Node old = xmlTerm;
			xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
			XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(location, 0), XmlLoader.getLocNumber(location, 1));
			XmlLoader.addFilename(xmlTerm, filename);
			XmlLoader.reportErrors(doc);

			old.getParentNode().replaceChild(old.getOwnerDocument().importNode(xmlTerm, true), old);

			NodeList list = doc.getElementsByTagName("cellSummary");
			for (int i = 0; i < list.getLength(); i++) {

				// Get element
				Element element = (Element) list.item(i);
				Cell cell = new Cell();

				// get color
				NamedNodeMap attr = element.getAttributes();

				Map<String, String> attrs = new HashMap<String, String>();
				for (int j = 0; j < attr.getLength(); j++) {
					Node nd = attr.item(j);
					attrs.put(nd.getNodeName(), nd.getNodeValue());
				}
				// TODO: just some checks
				// - check to see if sort conflicts with previous definition
				// - check to see if the color exists... etc
				cell.setLabel(attr.getNamedItem(Tag.value).getNodeValue());
				cell.setSort(attr.getNamedItem(Tag.maxSort).getNodeValue());
				cell.setAttributes(attrs);

				cellLabels.put(cell.getLabel(), cell);
			}

		} catch (Exception e) {
			e.printStackTrace();
			Error.report("Cannot parse configuration: " + e.getLocalizedMessage() + " at: " + this.location + " in file: " + this.filename);
		}

		parsed = true;
	}

	public Map<String, Cell> getCellLabels() {
		// if (!parsed) {
		// Error.report("Called getCellLabels before parsing the configuration! Please FIX me!!");
		// }

		return cellLabels;
	}

	public void setCellLabels(Map<String, Cell> cellLabels) {
		this.cellLabels = cellLabels;
	}

	@Override
	public SentenceType getType() {
		return SentenceType.CONFIGURATION;
	}

	public String getContent() {
		return content;
	}

	public void setContent(String content) {
		this.content = content;
	}

	public boolean isParsed() {
		return parsed;
	}
}
