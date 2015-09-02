// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.Cell;

import java.io.Serializable;
import java.util.Set;

/**
 * For each Cell, this class contains a reference to the cell itself, its id, a
 * link to its parent (if there exists), a {@line ConfigurationStructureMap}
 * mapping the name of its direct children to ConfigurationStructures, the
 * multiplicity of the cell, and the nesting level it can be found at.
 *
 * @author Traian
 */
public class ConfigurationStructure implements Serializable {
    public Cell cell;
    public String id;
    public Set<String> ancestorIds;
    public ConfigurationStructure parent = null;
    public ConfigurationStructureMap sons = new ConfigurationStructureMap();
    public Cell.Multiplicity multiplicity;
    public int level = 0;

    /**
     * Returns {@code true} if this cell has multiplicity='*' or multiplicity='+'
     */
    public boolean isStarOrPlus() {
        return multiplicity == Cell.Multiplicity.ANY || multiplicity == Cell.Multiplicity.SOME;
    }

    /**
     * Returns {@code true} if this cell should be present in the initial configuration or
     * on the right-hand side of rewrites.
     */
    public boolean isDefaultCell() {
        return multiplicity == Cell.Multiplicity.ONE
                || multiplicity == Cell.Multiplicity.SOME
                || cell.containsCellAttribute("initial");
    }

    public boolean hasChildren() {
        return !sons.isEmpty();
    }

    public boolean hasMultiplicityStarChildren() {
        return sons.keySet().stream()
                .anyMatch(l -> sons.get(l).multiplicity != Cell.Multiplicity.ONE);
    }
}
