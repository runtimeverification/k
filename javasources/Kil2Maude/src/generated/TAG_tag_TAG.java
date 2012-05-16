package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 * 
 */
public class TAG_tag_TAG extends Tag {

	public TAG_tag_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}

	@Override
	public String toMaude() throws Exception {
		// this should be repaired by Radu
		// now consider both cases value and str

		String tag = getElement().getAttribute(Constants.KEY_key_ATTR);
		String value = getElement().getAttribute(Constants.VALUE_value_ATTR);
		
		// ignore latex and cons for now
		if (tag.equals("latex"))
			return "";
		if (tag.equals("klabel"))
			return "";
		if (tag.equals("cons"))
			return "";
		
		
		if (value.equals(""))
			return tag + "=()";
		else if (value.startsWith("\""))
		{
			return tag + "=(" + value.substring(1, value.length() - 1) + ")";
		}
		else
			return tag + "=(" + value + ")";
	}
}
