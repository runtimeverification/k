package org.kframework.backend.latex;

import org.kframework.utils.general.GlobalSettings;
import org.kframework.kil.Rule;
import org.kframework.kil.Attributes;

public class DocumentationFilter extends LatexFilter {

	private String endl = System.getProperty("line.separator");
	
	public DocumentationFilter(org.kframework.kil.loader.Context context){
		super(context);
	}
    @Override
    public void visit(Rule rule) {
    	// termComment = false;
		Attributes atts = rule.getAttributes(); 
    	boolean process = false;
    	for(String tag : GlobalSettings.doctags){
    	    if(atts.containsKey(tag)){
    		    process = true;
    		    break;
    		}
    	}
		if(process){
	    	result.append("\\krule");
			if (!"".equals(rule.getLabel())) {
				result.append("[" + rule.getLabel() + "]");
			}
			result.append("{" + endl);
			rule.getBody().accept(this);
			result.append("}{");
			if (rule.getRequires() != null) {
				rule.getRequires().accept(this);
			}
			result.append("}{");
			if (rule.getEnsures() != null) {
				rule.getEnsures().accept(this);
			}
			result.append("}{");
			rule.getAttributes().accept(this);
			result.append("}");
			result.append("{");
			// if (termComment) result.append("large");
			result.append("}");
			result.append(endl);
		}
	}

}
