
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class CONTEXT_context_TAG extends Tag {

	public CONTEXT_context_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return "mb context " + processToMaudeAsSeparatedList("") + " : KSentence " + getMetadata() + " .";
	}

	private String getMetadata() {
		return "[metadata \"location=" + getElement().getAttribute(Constants.LOC_loc_ATTR) + "\"]";
	}
}
