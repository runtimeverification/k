
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.main.Maude;
import ro.uaic.fmse.k2m.main.StringUtil;
import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 *
 */
public class BUILTINOP_builtinOp_TAG extends Tag {

	public BUILTINOP_builtinOp_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		return getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR)) + "(" + processToMaudeAsSeparatedList(",") + ")";
	}
	
	@Override
	public String toAst() throws Exception {
		String content = processToASTAsSeparatedList(",");
		
		String sort = getElement().getAttribute(Constants.SORT_sort_ATTR);
		if (Maude.sortToSeparator.containsKey(sort))
			return "_" + StringUtil.escape(Maude.sortToSeparator.get(sort)) + "_(" + content + ")";
		
		if (content.equals(""))
			return getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR)) + "(.List{K})";
		
		return getConsMap().get(getElement().getAttribute(Constants.CONS_cons_ATTR)) + "(" + content + ")";
	}

}
