
package generated;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class CELL_cell_TAG extends Tag {

	private List<String> cellattributes;
	
	public CELL_cell_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
		
		cellattributes = new LinkedList<String>();

		cellattributes.add(Constants.MULTIPLICITY_multiplicity_ATTR);
		cellattributes.add(Constants.COLOR_color_ATTR);
		cellattributes.add(Constants.ELLIPSES_ellipses_ATTR);
	}
	
	@Override
	public String toMaude() throws Exception {
		String label = getElement().getAttribute(Constants.LABEL_label_ATTR);
//		String opened = getElement().getAttribute("opened");

		String labell = "<_>_</_>";
		
//		if (opened.equals("left"))
//			labell ="<_>..._</_>";
//		if (opened.equals("right"))
//			labell ="<_>_...</_>";
//		if (opened.equals("both"))
//			labell ="<_>..._...</_>";
		
		String head = "", start = "", end = "";
		for(String attr : cellattributes)
			if (!getElement().getAttribute(attr).equals(""))
			{
				start += "__(";
				end += ",_=_(" + attr + ",\""+ getElement().getAttribute(attr) + "\"))";
			}
		
		head = start + label + end;
				
		return labell + "(" + head + ", " + processToMaudeAsSeparatedList(", ") + ", " + label + ")";
	}
}
