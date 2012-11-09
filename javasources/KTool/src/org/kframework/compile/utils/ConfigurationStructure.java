package org.kframework.compile.utils;

import org.kframework.kil.Cell;

/**
* Initially created by: Traian Florin Serbanuta
* <p/>
* Date: 11/9/12
* Time: 10:35 PM
*/
public class ConfigurationStructure {
    public Cell cell;
    public String id;
    public ConfigurationStructure parent = null;
    public ConfigurationStructureMap sons = new ConfigurationStructureMap();
    public Cell.Multiplicity multiplicity;
    public int level = 0;
}
