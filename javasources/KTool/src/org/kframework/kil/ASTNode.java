package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformable;
import org.kframework.kil.visitors.Visitable;
import org.w3c.dom.Element;

public abstract class ASTNode implements Visitable,
		Transformable {
	protected Attributes attributes = null;


	public ASTNode(ASTNode di) {
		attributes = di.attributes;
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

    /*
    * methods for easy attributes manipulation
    * */
    public void addAttribute(String key, String value) {
        attributes.contents.add(new Attribute(key, value));
    }

    public void addAttribute(Attribute attribute) {
        attributes.contents.add(attribute);
    }

    public boolean containsAttribute(String key) {
        return attributes.containsKey(key);
    }

    public String getAttribute(String key) {
        return attributes.get(key);
    }

    public void putAttribute(String key, String value) {
        attributes.set(key, value);
    }

    public Attributes getAttributes() {
        return attributes;
    }

    public void setAttributes(Attributes attributes) {
        this.attributes = attributes;
    }


	public abstract ASTNode shallowCopy();
}
