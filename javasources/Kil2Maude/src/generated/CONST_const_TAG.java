
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class CONST_const_TAG extends Tag {

	public CONST_const_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		// return getElement().getAttribute(Constants.VALUE_value_ATTR);
		String sort = getElement().getAttribute(Constants.SORT_sort_ATTR);
		
		if (sort.equals("#Id"))
			return "#id_(\"" + getElement().getAttribute(Constants.VALUE_value_ATTR) + "\")";
//		else // if (sort.equals("#Int") || sort.equals("#String"))
//			constant = getElement().getAttribute(Constants.VALUE_value_ATTR) + "(.List{K})";
//		
//		return "# " + constant;
		return getElement().getAttribute(Constants.VALUE_value_ATTR);
	}
	
	@Override
	public String toAst() throws Exception {
		String sort = getElement().getAttribute(Constants.SORT_sort_ATTR);
		String constant = "";
		
		if (sort.equals("#Id"))
			constant = "#id_(\"" + getElement().getAttribute(Constants.VALUE_value_ATTR) + "\")(.List{K})";
		else // if (sort.equals("#Int") || sort.equals("#String"))
			constant = getElement().getAttribute(Constants.VALUE_value_ATTR) + "(.List{K})";
		
		return "# " + constant;
	}
}
