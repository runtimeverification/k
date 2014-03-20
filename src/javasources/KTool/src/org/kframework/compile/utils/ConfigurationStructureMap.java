package org.kframework.compile.utils;

import org.kframework.kil.Cell;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashMap;
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
    Map<String, ConfigurationStructure> config;

    public ConfigurationStructureMap() {
        this(new HashMap<String, ConfigurationStructure>());
    }

    public ConfigurationStructureMap(Map<String, ConfigurationStructure> config) {
        this.config = config;
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
        return config.get(o);
    }

    public ConfigurationStructure get(Cell o) {
        ConfigurationStructure cfgStr;
        cfgStr = config.get(o.getId());
        if (cfgStr == null) {
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                    KException.KExceptionGroup.INTERNAL,
                    "Cell " + o + " not found in configuration"
                    , this.getClass().getName(), o.getFilename(), o.getLocation()));
        }
        return cfgStr;
    }

    @Override
    public ConfigurationStructure put(String s, ConfigurationStructure configurationStructure) {
        if (config.containsKey(s)) {
            Cell c = config.get(s).cell;
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                    KException.KExceptionGroup.INTERNAL,
                    "Cell " + s + " found twice in configuration (once at " + c.getLocation() + ").", this.getClass().getName(),
                    configurationStructure.cell.getFilename(), configurationStructure.cell.getLocation()));
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
