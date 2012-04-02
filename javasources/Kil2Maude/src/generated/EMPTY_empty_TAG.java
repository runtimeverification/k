package generated;

import java.util.Map;


import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.main.Maude;
import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 * 
 */
public class EMPTY_empty_TAG extends Tag {

	public EMPTY_empty_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}

	@Override
	public String toMaude() throws Exception {
		String sort = getElement().getAttribute(Constants.SORT_sort_ATTR);

		if (Maude.sortToSeparator.containsKey(sort))
			return ".List`{\"" + Maude.sortToSeparator.get(sort) + "\"`}";

		if (Maude.basicSorts.contains(sort))
			return "(.)." + sort;

		return "." + sort;
	}
	
	@Override
	public String toAst() throws Exception {
		String sort = getElement().getAttribute(Constants.SORT_sort_ATTR);

		if (Maude.sortToSeparator.containsKey(sort))
			return "'.List`{\"" + Maude.sortToSeparator.get(sort) + "\"`}(.List{K})";
		// assume the separator is "" by default
		else return "'.List`{\"\"`}(.List{K})";
	}
}
