// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.Serializable;
import java.lang.annotation.Annotation;
import java.util.Scanner;
import java.util.Set;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.Attribute.Key;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

import com.google.common.reflect.TypeToken;
import com.google.inject.name.Names;

/**
 * Base class for K AST. Useful for Visitors and Transformers.
 */
public abstract class ASTNode implements Serializable {
    /**
     *
     */
    private static final long serialVersionUID = 1L;
    /**
     * Used on any node for metadata also used on {@link Rule} and {@link Production} for the attribute list.
     */
    private Attributes attributes;

    private Source source;
    private Location location;

    /**
     * Initializes an ASTNode from XML describing the parse tree
     *
     * @param elem
     *            The XML element describing the ASTNode
     */
    public ASTNode(Element elem) {
        this(getElementLocation(elem), getElementSource(elem));
    }

    /**
     * Retrieves the location from an XML element
     *
     * @param elem
     * @return the location stored in XML or Constants.GENERATED_LOCATION if no location found.
     */
    public static Location getElementLocation(Element elem) {
        if (elem != null && elem.hasAttribute(Constants.LOC_loc_ATTR)) {
            Scanner scanner = new Scanner(elem.getAttribute(Constants.LOC_loc_ATTR)).useDelimiter("[,)]").skip("\\(");
            int beginLine = scanner.nextInt();
            int beginCol = scanner.nextInt();
            int endLine = scanner.nextInt();
            int endCol = scanner.nextInt();
            return new Location(beginLine, beginCol, endLine, endCol);
        }
        else
            return null;
    }

    /**
     * Retrieves the file name from an XML element
     *
     * @param elem
     * @return the file name stored in XML or Constants.GENERATED_FILENAME if no filename found.
     */
    public static Source getElementSource(Element elem) {
        return (Source) elem.getUserData(Constants.SOURCE_ATTR);
    }

    /**
     * Copy constructor
     *
     * @param astNode
     */
    public ASTNode(ASTNode astNode) {
        copyAttributesFrom(astNode);
        location = astNode.location;
        source = astNode.source;
    }

    /**
     * Default constructor (generated at runtime)
     */
    public ASTNode() {
        this(null, null);
    }

    /**
     * Constructor with specified location and filename.
     *
     * @param loc
     * @param file
     */
    public ASTNode(Location loc, Source source) {
        setLocation(loc);
        setSource(source);
    }

    /**
     * Retrieves the location of the current ASTNode.
     *
     * @return recorded location or null if no recorded location found.
     */
    public Location getLocation() {
        return location;
    }

    /**
     * Sets the location or removes it if appropriate.
     *
     * @param loc
     */
    public void setLocation(Location location) {
        this.location = location;
    }

    /**
     * Retrieves the source of the current ASTNode.
     *
     * @return recorded source or null if no recorded source found.
     */
    public Source getSource() {
        return source;
    }

    /**
     * Sets the source or removes it if appropriate.
     *
     * @param file
     */
    public void setSource(Source source) {
        this.source = source;
    }

    /*
     * methods for easy attributes manipulation
     */

    /**
     * Appends an attribute to the list of attributes.
     *
     * @param key
     * @param val
     */
    public void addAttribute(String key, String val) {
        addAttribute(Attribute.of(key, val));
    }

    public <T> void addAttribute(Key<T> key, T val) {
        addAttribute(new Attribute<>(key, val));
    }

    public <T> void addAttribute(Class<T> key, T val) {
        addAttribute(Key.get(key), val);
    }

    public <T> void addAttribute(TypeToken<T> key, T val) {
        addAttribute(Key.get(key), val);
    }

    public <T> void addAttribute(TypeToken<T> key, Annotation annotation, T val) {
        addAttribute(Key.get(key, annotation), val);
    }

    public <T> void addAttribute(TypeToken<T> key, String annotation, T val) {
        addAttribute(Key.get(key, Names.named(annotation)), val);
    }

    public <T> void addAttribute(Class<T> key, Annotation annotation, T val) {
        addAttribute(Key.get(key, annotation), val);
    }

    public <T> void addAttribute(Class<T> key, String annotation, T val) {
        addAttribute(Key.get(key, Names.named(annotation)), val);
    }

    /**
     * Appends an attribute to the list of attributes.
     *
     * @param attr
     */
    public void addAttribute(Attribute<?> attr) {
        if (attributes == null)
            attributes = new Attributes();

        attributes.add(attr);
    }

    /**
     * @param key
     * @return whether the attribute key occurs in the list of attributes.
     */
    public boolean containsAttribute(String key) {
        if (attributes == null)
            return false;

        return attributes.containsKey(Attribute.keyOf(key));
    }


    /**
     * @param key
     * @return whether the attribute key occurs in the list of attributes.
     */
    public boolean containsAttribute(Key<?> key) {
        if (attributes == null)
            return false;

        return attributes.containsKey(key);
    }

    /**
     * Retrieves the attribute by key from the list of attributes
     *
     * @param key
     * @return a value for key in the list of attributes or the default value.
     */
    public String getAttribute(String key) {
        return getAttribute(Attribute.keyOf(key));
    }

    /**
     * Retrieves the attribute by key from the list of attributes
     *
     * @param key
     * @return a value for key in the list of attributes or the default value.
     */
    public <T> T getAttribute(Key<T> key) {
        if (attributes == null)
            return null;
        final Attribute<T> value = (Attribute<T>) attributes.get(key);
        if (value == null)
            return null;
        return value.getValue();
    }

    public <T> T getAttribute(Class<T> cls) {
        return getAttribute(Key.get(cls));
    }

    public <T> T getAttribute(Class<T> cls, Annotation annotation) {
        return getAttribute(Key.get(cls, annotation));
    }

    public <T> T getAttribute(Class<T> cls, String annotation) {
        return getAttribute(Key.get(cls, Names.named(annotation)));
    }

    public <T> T getAttribute(TypeToken<T> type) {
        return getAttribute(Key.get(type));
    }

    public <T> T getAttribute(TypeToken<T> type, Annotation annotation) {
        return getAttribute(Key.get(type, annotation));
    }

    public <T> T getAttribute(TypeToken<T> type, String annotation) {
        return getAttribute(Key.get(type, Names.named(annotation)));
    }

    /**
     * Updates the value of an attribute in the list of attributes.
     *
     * @param key
     * @param val
     */
    public void putAttribute(String key, String val) {
        addAttribute(key, val);
    }

    public void removeAttribute(String key) {
        getAttributes().remove(Attribute.keyOf(key));
    }

    /**
     * @return the attributes object associated to this ASTNode. Constructs one if it is
     * not already created.
     */
    public Attributes getAttributes() {
        if (attributes == null) {
            attributes = new Attributes();
        }
        return attributes;
    }

    /**
     * Sets the attributes object associated to this ASTNode.
     *
     * @param attrs
     */
    public void setAttributes(Attributes attrs) {
        attributes = attrs;
    }

    /**
     * Copies attributes from another node into this node.
     * Use this in preference to {@link ASTNode#getAttributes} where appropriate because
     * the latter will create a new object if no attributes exist.
     * @param node The ASTNode to copy all attributes from.
     */
    public void copyAttributesFrom(ASTNode node) {
        if (node.attributes == null)
            return;
        this.getAttributes().putAll(node.attributes);
    }

    /**
     * Retrieves the syntax production descendants of this ASTNode by attribute key.
     *
     * @param key
     * @return Set<Production> object containing the production descendants
     */
    public Set<Production> getSyntaxByTag(String key, Context context) {
        return SyntaxByTag.get(this, key, context);
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    public abstract ASTNode shallowCopy();

    protected abstract <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E;
}
