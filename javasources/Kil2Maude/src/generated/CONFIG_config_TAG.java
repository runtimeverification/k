
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class CONFIG_config_TAG extends Tag {

	public CONFIG_config_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return "mb configuration " + processToMaudeAsSeparatedList("") + " " + " : KSentence " + getMetadata() + " .";
	}

	private String getMetadata() {
		return "[metadata \"location=" + getElement().getAttribute(Constants.LOC_loc_ATTR) + "\"]";
	}
}
