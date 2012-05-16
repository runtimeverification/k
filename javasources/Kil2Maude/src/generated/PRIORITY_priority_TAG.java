
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class PRIORITY_priority_TAG extends Tag {

	public PRIORITY_priority_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return processToMaudeAsSeparatedList("\n");
	}
}
