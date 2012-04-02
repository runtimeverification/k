
package generated;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class DEFINE_define_TAG extends Tag {

	public DEFINE_define_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {

		// retrieve location
		String location = "";
		location = getElement().getAttribute(Constants.LOC_loc_ATTR);
		
		// retrieve the other attributes
		String tags = "";
		List<String> exceptions = new LinkedList<String>();
		exceptions.add(Constants.BODY_body_TAG);
		exceptions.add(Constants.COND_cond_TAG);
		tags = processToMaudeAsSeparatedListExceptions("", exceptions);

		// construct metadata
		String metadata = "[metadata \"function=() location=" + location + " " + tags + "\"]";
		
		// construct the rule body
		List<String> ignore = new LinkedList<String>();
		ignore.add(Constants.ANNOS_annos_TAG);
		return "mb rule " + processToMaudeAsSeparatedListExceptions(" ", ignore) + " : KSentence " + metadata + " .";

	}
	
	@Override
	public String toAst() throws Exception
	{
		// TODO Auto-generated method stub
		return super.toAst();
	}
}
