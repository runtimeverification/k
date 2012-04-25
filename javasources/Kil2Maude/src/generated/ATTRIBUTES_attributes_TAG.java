
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class ATTRIBUTES_attributes_TAG extends Tag {

	public ATTRIBUTES_attributes_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return processToMaudeAsSeparatedList(" ");
	}
	
	@Override
	public String toAst() throws Exception
	{
		// TODO Auto-generated method stub
		return super.toAst();
	}
}
