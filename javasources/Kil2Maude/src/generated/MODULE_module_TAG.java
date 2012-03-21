package generated;

import java.util.Map;
import java.util.Set;


import org.w3c.dom.Element;

import ro.uaic.fmse.k2m.main.Maude;
import ro.uaic.fmse.k2m.tag.Tag;

/**
 * @author andrei.arusoaie
 * 
 */
public class MODULE_module_TAG extends Tag {

	public MODULE_module_TAG(Element element, Map<String, String> consMap) {
		super(element, consMap);
	}

	@Override
	public String toMaude() throws Exception {
		String content = this.processToMaudeAsSeparatedList("\n");

		// ignore interfaces for builtin modules
		if (getElement().getAttribute(Constants.TYPE_type_ATTR).equals(
				"interface"))
			return "";

		// cell labels
		Set<String> cellLabels = getCellLabels();
		String clabels = "ops ";
		if (cellLabels == null || cellLabels.size() == 0)
			clabels = "";
		else {
			for (String label : cellLabels)
				clabels += label + " ";
			clabels += ": -> CellLabel .";
		}

		// subsorts to K
		Set<String> sorts = getSorts();
		String subsorts = "";
		if (sorts == null || sorts.size() == 0)
			subsorts = "";
		else {
			for (String sort : sorts)
				if (!Maude.mainSorts.contains(sort) && !sort.startsWith("#") && !Maude.sortToSeparator.containsKey(sort))
					subsorts += sort + " ";
			if (!subsorts.equals(""))
			subsorts = "subsorts " + subsorts + " < K .";
		}

		
		return "mod " + getModuleName() + " is\n" + content + "\n" + clabels+ "\n" 
				+ subsorts + "\nendm";
	}

	/**
	 * @return
	 */
	private String getModuleName() {
		return getElement().getAttribute(Constants.VALUE_value_ATTR);
	}
}
