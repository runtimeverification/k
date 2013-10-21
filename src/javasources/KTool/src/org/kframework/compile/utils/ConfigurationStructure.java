package org.kframework.compile.utils;

import org.kframework.kil.Cell;

import java.io.Serializable;

/**
 * For each Cell, this class contains a reference to the cell itself, its id, a link to its parent (if there exists),
 * a @see ConfigurationStructureMap mapping the name of its direct children to ConfigurationStructures, the multiplicity
 * of the cell, and the nesting level it can be found at.
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 11/9/12
 * Time: 10:35 PM
 */
public class ConfigurationStructure implements Serializable {
    public Cell cell;
    public String id;
    public ConfigurationStructure parent = null;
    public ConfigurationStructureMap sons = new ConfigurationStructureMap();
    public Cell.Multiplicity multiplicity;
    public int level = 0;
}
