/**
 * 
 */
package ro.uaic.info.fmse.k2m.tag;

import generated.Constants;
import generated.TagFactory;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import ro.uaic.info.fmse.k2m.interfaces.IAst;
import ro.uaic.info.fmse.k2m.interfaces.IMaude;

/**
 * @author andrei.arusoaie
 * 
 */
public abstract class Tag implements IMaude, IAst {
	private Element element;
	private Map<String, String> consMap;

	public Tag(Element element, Map<String, String> consMap) {
		this.element = element;
		this.setConsMap(consMap);
	}

	public List<Tag> getChildren() {
		List<Tag> children = new LinkedList<Tag>();

		NodeList nlist = element.getChildNodes();
		for (int i = 0; i < nlist.getLength(); i++) {
			if (nlist.item(i).getNodeType() == Node.ELEMENT_NODE) {
				Element element = (Element) nlist.item(i);

				children.add(TagFactory.createTag(element, consMap));
			}
		}

		return children;
	}

	public String processToMaudeAsSeparatedList(String separator)
			throws Exception {
		return processToMaudeAsSeparatedListExceptions(separator, new LinkedList<String>());
	}

	public String processToMaudeAsSeparatedListExceptions(String separator, List<String> exceptions)
			throws Exception {
		String out = "";
		List<Tag> children = getChildren();
		for (Tag tag : children) {
			if (tag != null && !exceptions.contains(tag.element.getNodeName()))
				out += tag.toMaude() + separator;
		}
		
		if (out.equals(""))
			return out;
		return out.substring(0, out.length() - separator.length());
	}
	
	public String processToASTAsSeparatedList(String separator)
			throws Exception {
		String out = "";
		List<Tag> children = getChildren();
		for (Tag tag : children) {
			if (tag != null)
				out += tag.toAst() + separator;
		}
		
		if (out.equals(""))
			return out;
		return out.substring(0, out.length() - separator.length());
	}


	
	public Tag getFirstChildByName(String name) {
		List<Tag> children = getChildren();
		for (Tag tag : children)
			if (tag.getElement().getNodeName().equals(name))
				return tag;
		return null;
	}

	public int countChildrenByName(String name) {
		int counter = 0;
		List<Tag> children = getChildren();
		for (Tag tag : children)
			if (tag.getElement().getNodeName().equals(name))
				counter++;
		return counter;

	}

	

	
	// retrieve cell labels
	public String getCellLabel() {
		if (getElement().getNodeName().equals(Constants.CELL_cell_TAG))
			return getElement().getAttribute(Constants.LABEL_label_ATTR);
		return null;
	}
	
	public Set<String> getCellLabels() {
		Set<String> labels = new HashSet<String>();
		
		List<Tag> children = getChildren();
		for (Tag tag : children)
			labels.addAll(tag.getCellLabels());
		
		String label = getCellLabel();
		if (label != null)
			labels.add(this.getCellLabel());

		return labels;
	}

	// KLabels
	public Set<String> getKLabels() {
		Set<String> klabels = new HashSet<String>();
		
		List<Tag> children = getChildren();
		for (Tag tag : children)
			klabels.addAll(tag.getKLabels());
		
		String klabel = getKLabel();
		if (klabel != null)
			klabels.add(this.getKLabel());

		return klabels;
	}
	
	private String getKLabel() {
		if (getElement().getNodeName().equals(Constants.CONST_const_TAG) && getElement().getAttribute(Constants.SORT_sort_ATTR).equals("KLabel"))
			return getElement().getAttribute(Constants.VALUE_value_ATTR);
		return null;
	}

	// retrieve sorts
	public String getSort()
	{
		if(getElement().getNodeName().equals(Constants.SORT_sort_TAG))
			return getElement().getAttribute(Constants.VALUE_value_ATTR);
		
		return null;
	}
	
	public Set<String> getSorts() {
		Set<String> sorts = new HashSet<String>();
		
		List<Tag> children = getChildren();
		for (Tag tag : children)
			sorts.addAll(tag.getSorts());
		
		String sort = getSort();
		if (sort != null)
			sorts.add(this.getSort());

		return sorts;
	}

	
	@Override
	public String toMaude() throws Exception {
//		if (false)
//			throw new Exception("Not Implemented!");
		return "";
	}
	
	@Override
	public String toAst() throws Exception {
		return null;
	}

	/**
	 * @return the consMap
	 */
	public Map<String, String> getConsMap() {
		return consMap;
	}

	/**
	 * @param consMap
	 *            the consMap to set
	 */
	public void setConsMap(Map<String, String> consMap) {
		this.consMap = consMap;
	}

	/**
	 * @return the element
	 */
	public Element getElement() {
		return element;
	}

	/**
	 * @param element
	 *            the element to set
	 */
	public void setElement(Element element) {
		this.element = element;
	}
}
