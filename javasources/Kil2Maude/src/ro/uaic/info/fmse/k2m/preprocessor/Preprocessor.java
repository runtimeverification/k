package ro.uaic.info.fmse.k2m.preprocessor;

import generated.Constants;

import java.util.LinkedList;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import ro.uaic.info.fmse.k2m.tag.NotGeneratedConstants;

public class Preprocessor {

	private List<String> productionRaiseUpAttributes;

	public Preprocessor() {
		productionRaiseUpAttributes = new LinkedList<String>();

		productionRaiseUpAttributes.add(NotGeneratedConstants.CONS);
//		productionRaiseUpAttributes.add("strict");
//		productionRaiseUpAttributes.add("seqstrict");
	}

	public Document setCons(Document doc) {
		NodeList productions = doc
				.getElementsByTagName(Constants.PRODUCTION_production_TAG);

		for (int i = 0; i < productions.getLength(); i++) {
			Element production = (Element) productions.item(i);

			NodeList annotations = production
					.getElementsByTagName(Constants.ANNOS_annos_TAG);
			for (int j = 0; j < annotations.getLength(); j++) {
				Element annotation = (Element) annotations.item(j);

				NodeList tags = annotation
						.getElementsByTagName(Constants.TAG_tag_TAG);
				for (int k = 0; k < tags.getLength(); k++) {
					Element tag = (Element) tags.item(k);
					String key = tag.getAttribute(Constants.KEY_key_ATTR);

					for (String pkey : productionRaiseUpAttributes)
						if (key.equals(pkey)) {
							production.setAttribute(pkey, tag
									.getAttribute(Constants.VALUE_value_ATTR));
						}
				}
			}
		}

		return doc;
	}

	public Document setSortToProduction(Document doc) {
		NodeList syntaxes = doc
				.getElementsByTagName(Constants.SYNTAX_syntax_TAG);

		for (int i = 0; i < syntaxes.getLength(); i++) {
			if (syntaxes.item(i).getNodeType() == Node.ELEMENT_NODE) {
				Element syntax = (Element) syntaxes.item(i);
				String mainSort = null;

				// get the syntax main sort
				NodeList sorts = syntax
						.getElementsByTagName(Constants.SORT_sort_TAG);
				for (int j = 0; j < sorts.getLength(); ) {
					// this should happen only once
					Element sort = (Element) sorts.item(j);
					mainSort = sort.getAttribute(Constants.VALUE_value_ATTR);
					break;
				}

				NodeList schildren = syntax.getChildNodes();
				for (int j = 0; j < schildren.getLength(); j++) {
					if (schildren.item(j).getNodeType() == Node.ELEMENT_NODE) {
						Element schild = (Element) schildren.item(j);

						if (schild.getNodeName().equals(
								Constants.PRODUCTION_production_TAG)) {
							if (mainSort != null)
								schild.setAttribute(NotGeneratedConstants.MAINSORT, mainSort);
						} else if (schild.getNodeName().equals(
								Constants.PRIORITY_priority_TAG)) {
							NodeList productions = schild.getChildNodes();
							for (int k = 0; k < productions.getLength(); k++) {
								if (productions.item(k).getNodeType() == Node.ELEMENT_NODE) {
									Element production = (Element) productions
											.item(k);
									if (mainSort != null)
										production.setAttribute(NotGeneratedConstants.MAINSORT,
												mainSort);
								}
							}
						}
					}
				}
			}
		}

		return doc;
	}

	public Document addMaudeLabels(Document doc) {
		NodeList productions = doc
				.getElementsByTagName(Constants.PRODUCTION_production_TAG);
		for (int i = 0; i < productions.getLength(); i++) {
			Element production = (Element) productions.item(i);

			String maudeLabel = "";
			boolean isList = false;
			int sortNo = 0, terminalNo = 0;

			NodeList children = productions.item(i).getChildNodes();
			for (int j = 0; j < children.getLength(); j++) {
				if (children.item(j).getNodeType() == Node.ELEMENT_NODE) {
					if (children.item(j).getNodeName()
							.equals(Constants.SORT_sort_TAG)) {
						maudeLabel += "_";
						sortNo++;
					} else if (children.item(j).getNodeName()
							.equals(Constants.TERMINAL_terminal_TAG)) {
						maudeLabel += ((Element) children.item(j))
								.getAttribute(Constants.VALUE_value_ATTR);
						terminalNo++;
					} else if (children.item(j).getNodeName()
							.equals(Constants.USERLIST_userlist_TAG)) {
						Element ulist = (Element) children.item(j);
						String separator = ulist
								.getAttribute(Constants.SEPARATOR_separator_ATTR);
						maudeLabel = "_" + separator + "_";
						isList = true;
						break;
					}
				}
			}

			if (sortNo == 1 && terminalNo == 0)
				production.setAttribute(NotGeneratedConstants.ISSUBSORT, "true");
			else if (isList) {
				production.setAttribute(NotGeneratedConstants.ISLIST, "true");
				production.setAttribute(NotGeneratedConstants.LABEL, maudeLabel);
			} else {
				production.setAttribute(NotGeneratedConstants.LABEL, maudeLabel);
				production.setAttribute(NotGeneratedConstants.ISOP, "true");
			}
		}

		return doc;
	}

	public Document setAnnotationsForUserlist(Document doc)
	{
		NodeList productions = doc.getElementsByTagName(Constants.PRODUCTION_production_TAG);
		
		for(int i = 0; i < productions.getLength(); i++)
		{
			Element production = (Element)productions.item(i);
			Element annotation = null;
			
			NodeList annotations = production.getElementsByTagName(Constants.ANNOS_annos_TAG);
			for (int j = 0; j < annotations.getLength();)
			{
				// there should be only one annotation per production
				annotation = (Element)annotations.item(j);
				break;
			}
			
			Element list = null;
			NodeList lists = production.getElementsByTagName(Constants.USERLIST_userlist_TAG);
			for (int j = 0; j < lists.getLength();)
			{
				// there should be only one annotation per production
				list = (Element)lists.item(j);
				break;
			}
			
			if (list != null && annotation != null)
			{
				list.appendChild(annotation.cloneNode(true));
				list.setAttribute(NotGeneratedConstants.MAINSORT, production.getAttribute(NotGeneratedConstants.MAINSORT));
			}
		}
		
		return doc;
	}
	

	private Document setMainSortToUserlists(Document doc) {
		NodeList productions = doc.getElementsByTagName(Constants.PRODUCTION_production_TAG);
		
		for(int i = 0; i < productions.getLength(); i++)
		{
			Element production = (Element)productions.item(i);
			
			NodeList userlists = production.getElementsByTagName(Constants.USERLIST_userlist_TAG);
			for(int j = 0; j < userlists.getLength(); j++)
			{
				Element ulist = (Element)userlists.item(j);
				ulist.setAttribute(NotGeneratedConstants.MAINSORT, production.getAttribute(NotGeneratedConstants.MAINSORT));
			}
		}
		
		return doc;
	}

	
	public Document process(Document doc) {

		// do not change the order of these function calls
		// most of them depend on the steps above
		
		// raise the cons to production level: it is much easier to retrieve the cons on production than searching it into children
		doc = setCons(doc);

		// propagate the sorts to each production such that op label : sorts -> SORT . to be easily generated
		doc = setSortToProduction(doc);

		// add maude labels: generates maude-like labels (_+_) for each production
		doc = addMaudeLabels(doc);

		// set annotations for list productions to userlist for displaying easily metadata for userlists
		doc = setAnnotationsForUserlist(doc);
		
		// set the main sort of a production to userlists
		doc = setMainSortToUserlists(doc);
		
		// System.out.println(XmlFormatter.format(doc));
//		FileUtil.saveInFile("fifi.xml", XmlFormatter.format(doc));
		// System.exit(1);
		return doc;
	}
}
