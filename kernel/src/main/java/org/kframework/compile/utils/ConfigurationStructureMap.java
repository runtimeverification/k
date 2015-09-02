// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.Cell;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * A Map from cell names to {@link ConfigurationStructure} representing the cell
 * contents and attributes.
 *
 * @author Traian
 */
public class ConfigurationStructureMap extends LinkedHashMap<String, ConfigurationStructure> implements Serializable {

    public ConfigurationStructure get(Cell o) {
        ConfigurationStructure cfgStr;
        cfgStr = get(o.getId());
        if (cfgStr == null) {
            throw KExceptionManager.internalError(
                    "Cell " + o + " not found in configuration", o);
        }
        return cfgStr;
    }

    /**
     * Returns the position of a cell declared under the {@code Cell} of this
     * {@code ConfigurationStructureMap}.
     *
     * @param cellLabel
     *            the cell label
     * @return if found, the position of the cell starting from 0; otherwise, -1
     */
    public int positionOf(String cellLabel) {
        int pos = -1;
        for (String l : keySet()) {
            pos++;
            if (l.equals(cellLabel)) {
                return pos;
            }
        }
        return -1;
    }

    public Set<String> descendants(String cellName) {
        Set<String> descendants = new HashSet<>();
        if (containsKey(cellName)) {
            descendants.add(cellName);
            get(cellName).sons.keySet().stream()
                    .map(this::descendants)
                    .forEach(descendants::addAll);
        }
        return descendants;
    }

    @Override
    public ConfigurationStructure put(String s, ConfigurationStructure configurationStructure) {
        if (containsKey(s)) {
            Cell c = get(s).cell;
            throw KExceptionManager.internalError(
                    "Cell " + s + " found twice in configuration (once at " + c.getLocation() + ").",
                    configurationStructure.cell);
        }
        return super.put(s, configurationStructure);
    }

}
