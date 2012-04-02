
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
public class KAPP_KApp_TAG extends Tag {

	public KAPP_KApp_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		
		List<String> exceptions = new LinkedList<String>();
		exceptions.add(Constants.LISTOFK_ListOfK_TAG);
		String theLabel = processToMaudeAsSeparatedListExceptions("", exceptions);
		
		exceptions = new LinkedList<String>();
		exceptions.add(Constants.LABEL_label_TAG);
		String theListOfK = processToMaudeAsSeparatedListExceptions(",,", exceptions);
		
		return theLabel + "(" + theListOfK + ")";
	}
	
	@Override
	public String toAst() throws Exception
	{
		// TODO Auto-generated method stub
		return super.toAst();
	}
}
