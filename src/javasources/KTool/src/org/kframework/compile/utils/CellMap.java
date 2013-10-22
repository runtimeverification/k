package org.kframework.compile.utils;

import java.io.Serializable;


/**
 * @author AndreiS
 */
public class CellMap implements Serializable {

    private final String mapCellLabel;
    private final String entryCellLabel;
    private final String keyCellLabel;

    public CellMap(String mapCellLabel, String entryCellLabel, String keyCellLabel) {
        this.mapCellLabel = mapCellLabel;
        this.entryCellLabel = entryCellLabel;
        this.keyCellLabel = keyCellLabel;
    }

    public String mapCellLabel() {
        return mapCellLabel;
    }

    public String entryCellLabel() {
        return entryCellLabel;
    }

    public String keyCellLabel() {
        return keyCellLabel;
    }

}
