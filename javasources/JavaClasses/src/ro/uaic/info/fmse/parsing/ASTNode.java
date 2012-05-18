package ro.uaic.info.fmse.parsing;

import org.w3c.dom.Element;

import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.transitions.maude.IMaude;
import ro.uaic.info.fmse.transitions.xml.IXML;

public abstract class ASTNode implements IMaude, IXML, Modifiable, Visitable {
	protected String location;
	protected String filename;

	public ASTNode(String location, String filename) {
		this.location = location;
		this.filename = filename;
	}

	public ASTNode(Element element) {
		if (element != null) {
			this.filename = element.getAttribute(Constants.FILENAME_filename_ATTR);
			this.location = element.getAttribute(Constants.LOC_loc_ATTR);
		}
	}

	public String getMaudeLocation() {
		String location = this.location;
		location = location.replaceAll(",", ":");
		location = location.replaceFirst("\\(", "(" + this.filename + ":");
		return location;
	}

	public abstract void applyToAll(Modifier visitor);

	public String getLocation() {
		return location;
	}

	public void setLocation(String location) {
		this.location = location;
	}

	public String getFilename() {
		return filename;
	}

	public void setFilename(String filename) {
		this.filename = filename;
	}
	
}
