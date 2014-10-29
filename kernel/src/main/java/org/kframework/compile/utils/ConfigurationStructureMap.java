// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.Cell;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.io.Serializable;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * A Map from cell names to {@link ConfigurationStructure} representing the cell
 * contents and attributes.
 *
 * @author Traian
 */
public class ConfigurationStructureMap implements
        Map<String, ConfigurationStructure>, Serializable {
    LinkedHashMap<String, ConfigurationStructure> config;

    public ConfigurationStructureMap() {
        this.config = new LinkedHashMap<String, ConfigurationStructure>();
    }

    @Override
    public int size() {
        return config.size();
    }

    @Override
    public boolean isEmpty() {
        return config.isEmpty();
    }

    @Override
    public boolean containsKey(Object o) {
        return config.containsKey(o);
    }

    @Override
    public boolean containsValue(Object o) {
        return config.containsValue(o);
    }

    @Override
    public  ConfigurationStructure get(Object o) {
        assert o instanceof String : "unexpected argument type "
                + o.getClass().getName() + "; expected String";
        return config.get(o);
    }

    public ConfigurationStructure get(Cell o) {
        ConfigurationStructure cfgStr;
        cfgStr = config.get(o.getId());
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
        for (String l : config.keySet()) {
            pos++;
            if (l.equals(cellLabel)) {
                return pos;
            }
        }
        return -1;
    }

    @Override
    public ConfigurationStructure put(String s, ConfigurationStructure configurationStructure) {
        if (config.containsKey(s)) {
            Cell c = config.get(s).cell;
            throw KExceptionManager.internalError(
                    "Cell " + s + " found twice in configuration (once at " + c.getLocation() + ").",
                    configurationStructure.cell);
        }
        return config.put(s,configurationStructure);
    }

    @Override
    public ConfigurationStructure remove(Object o) {
        return config.remove(o);
    }

    @Override
    public void putAll(Map<? extends String, ? extends ConfigurationStructure> map) {
        config.putAll(map);
    }

    @Override
    public void clear() {
        config.clear();
    }

    @Override
    public Set<String> keySet() {
        return config.keySet();
    }

    @Override
    public Collection<ConfigurationStructure> values() {
        return config.values();
    }

    @Override
    public Set<Entry<String, ConfigurationStructure>> entrySet() {
        return config.entrySet();
    }
}
