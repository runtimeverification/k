
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class BAG_Bag_TAG extends Tag {

	public BAG_Bag_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		if (getChildren().size() == 1)
			return processToMaudeAsSeparatedList("");
		
		return "__(" + processToMaudeAsSeparatedList(",") + ")";
	}
}
