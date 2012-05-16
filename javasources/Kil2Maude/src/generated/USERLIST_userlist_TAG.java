
package generated;

import java.util.Map;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.k2m.main.Maude;
import ro.uaic.info.fmse.k2m.tag.NotGeneratedConstants;
import ro.uaic.info.fmse.k2m.tag.Tag;
import ro.uaic.info.fmse.utils.strings.StringUtil;

/**
 * @author andrei.arusoaie
 *
 */
public class USERLIST_userlist_TAG extends Tag {

	public USERLIST_userlist_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}
	
	@Override
	public String toMaude() throws Exception {
		
		String sort = this.getElement().getAttribute(Constants.VALUE_value_ATTR);
		String separator = getElement().getAttribute(Constants.SEPARATOR_separator_ATTR);
		String listSort = getElement().getAttribute(NotGeneratedConstants.MAINSORT);
		String metadata = getMetadata();
		
		String decl = "";
		if (!(Maude.listSeparators.contains(separator)))
		{
			if (!metadata.equals(""))
				metadata = "metadata \"" + metadata + " hybrid=()\"";
			// declare op and eq for separator
			decl += "op _" + StringUtil.escape(separator) + "_ : K K -> K [prec 120 " + metadata + "] .\n";
			decl += "op .List`{\"" + separator + "\"`} : -> K .\n";
			decl += "eq 'isKResult(.List`{\"" + separator + "\"`}) = true .\nop 'isKResult : -> KLabel [metadata \"generated-label=()\"] .\n";
			
			// store the separator
			Maude.listSeparators.add(separator);
		}
		
		decl += "subsort "+listSort+" < K .\n";
		decl += "op 'is"+listSort+" : -> KLabel .\n";
		decl += "eq 'is"+listSort+"(.List`{\""+separator+"\"`}) = true .\n";
//		decl += "eq 'is"+listSort+"(( X:" + sort + " " + separator + " L:"+listSort+" )) = true .\n";
		decl += "eq 'is"+listSort+"(_" + StringUtil.escape(separator) + "_( X:" + sort + ", L:" + listSort + " )) = true .\n";
		
		return decl;
	}

	private String getMetadata()
	{
		try
		{
			return processToMaudeAsSeparatedList(" ");
		} catch (Exception e)
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return "";
	}
}
