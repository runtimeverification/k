package generated;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;


import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.main.Maude;
import ro.uaic.info.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 * 
 */
public class SYNTAX_syntax_TAG extends Tag {

	public SYNTAX_syntax_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}

	@Override
	public String toMaude() throws Exception {
		
		// get sort 
		String sort = "";
		List<String> excepts = new LinkedList<String>();
		excepts.add(Constants.PRIORITY_priority_TAG);
		sort = processToMaudeAsSeparatedListExceptions("", excepts);
		
		// get content
		String content = "";
		List<String> except = new LinkedList<String>();
		except.add(Constants.SORT_sort_TAG);
		content += processToMaudeAsSeparatedListExceptions("\n", except);
		
		// sort declaration
		if (Maude.declaredSorts.contains(sort))
			sort = "";
		else if (sort.startsWith("#")) {
			Maude.declaredSorts.add(sort);
			sort = "";
		} else {
			Maude.declaredSorts.add(sort);
			sort = "sort " + sort + " .\n";
		}

		// return declaration and operation/subsort (s)
		return sort + content;
	}
}
