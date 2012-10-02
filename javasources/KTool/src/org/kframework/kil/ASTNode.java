package org.kframework.kil;

import org.kframework.backend.maude.IMaude;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Modifiable;
import org.kframework.kil.visitors.Modifier;
import org.kframework.kil.visitors.Transformable;
import org.kframework.kil.visitors.Visitable;
import org.w3c.dom.Element;


public abstract class ASTNode implements IMaude, Modifiable, Visitable,
		Transformable {
	protected Attributes attributes = null;


	public ASTNode(ASTNode di) {
		this.attributes = di.attributes;
	}

	public ASTNode(String location, String filename) {
		init(location, filename);
	}

	private void init(String location, String filename) {
		setLocation(location);
		setFilename(filename);
	}

	public ASTNode(Element element) {
		if (element != null) {
			init( element.getAttribute(Constants.LOC_loc_ATTR),
					element.getAttribute(Constants.FILENAME_filename_ATTR));
		}
	}

	public ASTNode() {
		init(Constants.GENERATED_LOCATION, Constants.GENERATED_FILENAME);	
	}

	public String getMaudeLocation() {
		String location = getLocation();
		location = location.replaceAll(",", ":");
		location = location.replaceFirst("\\(", "(" + getFilename() + ":");
		if (!location.startsWith("(")) location = "(" + location + ")";

		return location;
	}

	public abstract void applyToAll(Modifier visitor);

	public String getLocation() {
		if (null == attributes) return Constants.GENERATED_LOCATION;
		String loc = attributes.get("location");
		if (null == loc) return Constants.GENERATED_LOCATION;
		return loc;
	}

	public void setLocation(String location) {
		if (location.equals(Constants.GENERATED_LOCATION)) return;
		if (null == attributes) attributes = new Attributes();
		attributes.set("location",location);
	}

	public String getFilename() {
		if (null == attributes) return Constants.GENERATED_FILENAME;
		String file = attributes.get("filename");
		if (null == file) return Constants.GENERATED_FILENAME;
		return file;
	}

	public void setFilename(String filename) {
		if (filename.equals(Constants.GENERATED_FILENAME)) return;
		if (null == attributes) attributes = new Attributes();
		attributes.set("filename", filename);
	}

	public abstract ASTNode shallowCopy();
}
