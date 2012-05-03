package ro.uaic.info.fmse.parsing;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.transitions.maude.IMaude;

public abstract class ASTNode extends IMaude{
	protected String location;
	protected String filename;

	public ASTNode(Element element) {
		this.filename = element.getAttribute(Constants.FILENAME_filename_ATTR);
		this.location = element.getAttribute(Constants.LOC_loc_ATTR);
	}
}
