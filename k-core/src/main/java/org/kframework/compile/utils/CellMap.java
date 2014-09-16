// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.CellDataStructure;


/**
 * @author AndreiS
 */
public class CellMap extends CellDataStructure {

    private final String entryCellLabel;
    private final String keyCellLabel;

    public CellMap(String mapCellLabel, String entryCellLabel, String keyCellLabel) {
        super(mapCellLabel);
        this.entryCellLabel = entryCellLabel;
        this.keyCellLabel = keyCellLabel;
    }

    public String entryCellLabel() {
        return entryCellLabel;
    }

    public String keyCellLabel() {
        return keyCellLabel;
    }

}
