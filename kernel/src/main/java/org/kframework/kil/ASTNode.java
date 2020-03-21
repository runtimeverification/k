// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

import java.io.Serializable;
import java.util.Optional;

/**
 * Base class for K AST. Useful for Visitors and Transformers.
 */
public abstract class ASTNode implements Serializable, HasLocation {
    /**
     *
     */
    private static final long serialVersionUID = 1L;
    /**
     * Used on any node for metadata also used on {@link Rule} and {@link Production} for the attribute list.
     */
    private Att att = Att.empty();

    private Source source;
    private Location location;

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

    public Optional<Location> location() { return Optional.ofNullable(location); }
    public Optional<Source> source() { return Optional.ofNullable(source); }

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
        att = att.add(key, val);
    }

    /**
     * @param key
     * @return whether the attribute key occurs in the list of attributes.
     */
    public boolean containsAttribute(String key) {
        return att.contains(key);
    }


    /**
     * Retrieves the attribute by key from the list of attributes
     *
     * @param key
     * @return a value for key in the list of attributes or the default value.
     */
    public String getAttribute(String key) {
        return att.getOptional(key).orElse(null);
    }

    /**
     * @return the attributes object associated to this ASTNode. Constructs one if it is
     * not already created.
     */
    public Att getAttributes() {
        return att;
    }

}
