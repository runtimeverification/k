package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.Transformable;
import org.kframework.kil.visitors.Visitable;
import org.w3c.dom.Element;

public abstract class ASTNode implements Visitable, Transformable {
    // attributes non-null
	protected Attributes attributes;

    public ASTNode(Element elem) {
        this(getElementLocation(elem), getElementFile(elem));
    }

    private static String getElementLocation(Element elem) {
        if (elem != null)
            return elem.getAttribute(Constants.LOC_loc_ATTR);
        else
            return Constants.GENERATED_LOCATION;
    }

    private static String getElementFile(Element elem) {
        if (elem != null)
            return elem.getAttribute(Constants.FILENAME_filename_ATTR);
        else
            return Constants.GENERATED_FILENAME;
    }

    public ASTNode(ASTNode astNode) {
		attributes = astNode.attributes;
	}

	public ASTNode() {
		this(Constants.GENERATED_LOCATION, Constants.GENERATED_FILENAME);
	}

    public ASTNode(String loc, String file) {
        //attributes = new Attributes();
        setLocation(loc);
        setFilename(file);
    }


	public String getMaudeLocation() {
		String loc = getLocation();
		loc = loc.replaceAll(",", ":");
		loc = loc.replaceFirst("\\(", "(" + getFilename() + ":");
		if (!loc.startsWith("("))
            loc = "(" + loc + ")";

		return loc;
	}

	public String getLocation() {
        // next if statement should be unnecessary
        if (attributes == null)
            return Constants.GENERATED_LOCATION;

		String loc = attributes.get("location");
		if (loc == null)
            loc = Constants.GENERATED_LOCATION;
		return loc;
	}

	public void setLocation(String loc) {
        // next 2 if statements should be unnecessary
		if (loc.equals(Constants.GENERATED_LOCATION))
            return;
        if (attributes == null)
            attributes = new Attributes();

        attributes.set("location", loc);
	}

	public String getFilename() {
        // next if statement should be unnecessary
        if (attributes == null)
            return Constants.GENERATED_FILENAME;

		String file = attributes.get("filename");
		if (file == null)
            file = Constants.GENERATED_FILENAME;
		return file;
	}

	public void setFilename(String file) {
        // next 2 if statements should be unnecessary
		if (file.equals(Constants.GENERATED_FILENAME))
            return;
        if (attributes == null)
            attributes = new Attributes();

		attributes.set("filename", file);
	}

    /*
   * methods for easy attributes manipulation
   * */
    public void addAttribute(String key, String val) {
        addAttribute(new Attribute(key, val));
    }

    public void addAttribute(Attribute attr) {
        if (attributes == null)
            attributes = new Attributes();

        attributes.contents.add(attr);
    }

    public boolean containsAttribute(String key) {
        if (attributes == null)
            return false;

        return attributes.containsKey(key);
    }

    public String getAttribute(String key) {
        if (attributes == null)
            return null;

        return attributes.get(key);
    }

    public void putAttribute(String key, String val) {
        if (attributes == null)
            attributes = new Attributes();

        attributes.set(key, val);
    }

    public Attributes getAttributes() {
        return attributes;
    }

    public void setAttributes(Attributes attrs) {
        attributes = attrs;
    }


	public abstract ASTNode shallowCopy();
}
