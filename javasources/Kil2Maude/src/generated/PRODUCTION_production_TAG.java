package generated;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;


import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.main.StringUtil;
import ro.uaic.fmse.k2m.tag.NotGeneratedConstants;
import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 * 
 */
public class PRODUCTION_production_TAG extends Tag {

	public PRODUCTION_production_TAG(Element element,
			Map<String, String> consMap) {
		super(element, consMap);
	}

	@Override
	public String toMaude() throws Exception {

		boolean isSubsort = !"".equals(getElement().getAttribute(NotGeneratedConstants.ISSUBSORT));
		if (isSubsort)
		{
			String sorts = processToMaudeAsSeparatedList(" ");
			return "subsort " + sorts + " < " + getElement().getAttribute(NotGeneratedConstants.MAINSORT) + " .";
		}

		boolean isList = !"".equals(getElement().getAttribute(NotGeneratedConstants.ISLIST));
		if (isList)
		{
			// ignore list
			List<String> ignore = new LinkedList<String>();
			ignore.add(Constants.SORT_sort_TAG);
			ignore.add(Constants.TERMINAL_terminal_TAG);
			ignore.add(Constants.ANNOS_annos_TAG);

			String thelist = processToMaudeAsSeparatedListExceptions("", ignore);
			return thelist;
		}

		boolean isOp = !"".equals(getElement().getAttribute(NotGeneratedConstants.ISOP)) && !"".equals(getElement().getAttribute(NotGeneratedConstants.CONS));
		if(isOp)
		{
			String maudeLabel = getElement().getAttribute(NotGeneratedConstants.LABEL);
			String sort = getElement().getAttribute(NotGeneratedConstants.MAINSORT);
			String location = getElement().getAttribute(Constants.LOC_loc_ATTR);
			
			// ignore list
			List<String> ignore = new LinkedList<String>();
			ignore.add(Constants.SORT_sort_TAG);
			ignore.add(Constants.TERMINAL_terminal_TAG);
			ignore.add(Constants.USERLIST_userlist_TAG);
			String tags = processToMaudeAsSeparatedListExceptions("", ignore);
			
			String metadata = " [metadata \"" + tags + " location="
					+ location + "\"]";
			
			return "op " + StringUtil.escape(maudeLabel) + " : " + getSubSorts() + " -> " + sort + metadata + " .\n";
		}
		
		return "";
	}

	private String getSubSorts()
	{
		String out = "";
		List<Tag> children = getChildren();
		for(Tag tag:children)
			if (tag.getElement().getNodeName().equals(Constants.SORT_sort_TAG))
				out += tag.getElement().getAttribute(Constants.VALUE_value_ATTR) + " ";
		
		return out.trim();
	}
}
