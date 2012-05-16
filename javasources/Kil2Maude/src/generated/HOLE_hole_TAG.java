
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class HOLE_hole_TAG extends Tag {

	public HOLE_hole_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return "HOLE";
	}
}
