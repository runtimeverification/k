
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class SETITEM_SetItem_TAG extends Tag {

	public SETITEM_SetItem_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return "SetItem(" + processToMaudeAsSeparatedList("") + ")";
	}
}
