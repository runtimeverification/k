package ro.uaic.info.fmse.pp.labels;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import ro.uaic.info.fmse.utils.strings.StringUtil;

public class LabelGenerator {

	private static final String PRODUCTION = "production";
	private static final String ATTRIBUTES = "attributes";
	private static final String TAG = "tag";
	private static final String KLABEL = "klabel";
	private static final String KEY = "key";
	private static final String SORT = "sort";
	private static final String TERMINAL = "terminal";
	private static final String USERLIST = "userlist";
	private static final String SEPARATOR = "separator";
	private static final String VALUE = "value";
	private static final String LOCATION = "location";

	public Document generateKLabels(Document doc) {
		// get all the productions and check them
		NodeList productions = doc.getElementsByTagName(PRODUCTION);
		
		for (int i = 0; i < productions.getLength(); i++) {
			Element production = (Element) productions.item(i);

			// theoretically there should be only one such tag
			NodeList attributes = production.getElementsByTagName(ATTRIBUTES);

			for (int j = 0; j < attributes.getLength(); j++) {
				Element attribute = (Element) attributes.item(j);

				// check if the user already declared a klabel
				NodeList tags = attribute.getElementsByTagName(TAG);

				boolean declared = false;
				for (int k = 0; k < tags.getLength(); k++) {
					Element tag = (Element) tags.item(k);

					String key = tag.getAttribute("key");
					if (key.equals(KLABEL))
						declared = true;
				}

				if (!declared) {
					// compute the production label by concatenating "_" instead
					// of sorts and the terminal values.
					String generatedLabel = StringUtil.escape(computeKLabel(production));
					if (!generatedLabel.equals("")) { // subsorts are ignored
						// append a new tag element with the generated cons
						Element element = doc.createElement(TAG);

						// set it up
						element.setAttribute(KEY, KLABEL);
						element.setAttribute(VALUE, generatedLabel);
						element.setAttribute(LOCATION, "generated");

						// append it as a child of attribute
						attribute.appendChild(element);
					}
				}
			}
		}

		return doc;
	}

	private String computeKLabel(Element production) {
		String maudeLabel = "";
		int sortNo = 0;
		int terminalNo = 0;

		NodeList children = production.getChildNodes();
		for (int j = 0; j < children.getLength(); j++) {
			if (children.item(j).getNodeType() == Node.ELEMENT_NODE) {
				if (children.item(j).getNodeName().equals(SORT)) {
					maudeLabel += "_";
					sortNo++;
				} else if (children.item(j).getNodeName().equals(TERMINAL)) {
					maudeLabel += ((Element) children.item(j))
							.getAttribute(VALUE);
					terminalNo++;
				} else if (children.item(j).getNodeName().equals(USERLIST)) {
					Element ulist = (Element) children.item(j);
					String separator = ulist.getAttribute(SEPARATOR);
					maudeLabel = "_" + separator + "_";
					break;
				}
			}
		}

		if (sortNo == 1 && terminalNo == 0)
			return "";

		return maudeLabel;
	}
}
