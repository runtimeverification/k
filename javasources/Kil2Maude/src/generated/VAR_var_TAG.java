
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class VAR_var_TAG extends Tag {

	public VAR_var_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		
		// _ => ?
		String name = getElement().getAttribute(Constants.NAME_name_ATTR);
		
		if (name.equals("_"))
			name = "?";
		
		return name + ":" + getElement().getAttribute(Constants.SORT_sort_ATTR);
	}
}
