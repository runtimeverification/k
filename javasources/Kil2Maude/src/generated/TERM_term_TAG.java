
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.main.Maude;
import ro.uaic.info.fmse.k2m.tag.Tag;
import ro.uaic.info.fmse.utils.strings.StringUtil;

/**
 * @author andrei.arusoaie
 *
 */
public class TERM_term_TAG extends Tag {

	public TERM_term_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		String content = processToMaudeAsSeparatedList(",");
		
		if (content.equals(""))
			return getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR));
		
		return getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR)) + "(" + content + ")";
	}
	
	@Override
	public String toAst() throws Exception {
		String content = processToASTAsSeparatedList(",,");
		
		String sort = getElement().getAttribute(Constants.SORT_sort_ATTR);
		if (Maude.sortToSeparator.containsKey(sort))
			return "'_" + StringUtil.escape(Maude.sortToSeparator.get(sort)) + "_(" + content + ")";
		
		if (content.equals(""))
			return "'" + getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR)) + "(.List{K})";
		
		return "'" + getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR)) + "(" + content + ")";
	}
}
