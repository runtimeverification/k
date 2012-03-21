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
public class RULE_rule_TAG extends Tag {

	public RULE_rule_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}

	@Override
	public String toMaude() throws Exception {

		String ruleName = getElement().getAttribute(Constants.LABEL_label_ATTR);
		
		// retrieve rule location
		String location = "";
		location = getElement().getAttribute(Constants.LOC_loc_ATTR);
		
		// retrieve the other attributes
		String tags = "";
		List<String> exceptions = new LinkedList<String>();
		exceptions.add(Constants.BODY_body_TAG);
		exceptions.add(Constants.COND_cond_TAG);
		tags = processToMaudeAsSeparatedListExceptions("", exceptions);

		// construct metadata
		// ruleName is a bit special: it must in metadata and maude attribute
		String metadata = "";
		if (!ruleName.equals(""))
			metadata = "[metadata \"location=" + location + " " + tags + " " + ruleName + "=()\" label " + ruleName + "]";
		else metadata = "[metadata \"location=" + location + " " + tags + "\"]";
		
		// construct the rule body
		List<String> ignore = new LinkedList<String>();
		ignore.add(Constants.ANNOS_annos_TAG);
		return "mb rule " + processToMaudeAsSeparatedListExceptions(" ", ignore) + " : KSentence " + metadata + " .";
		
	}
}
