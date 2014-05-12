// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.Serializable;

/**
 * @author AndreiS
 */
public class CellDataStructure implements Serializable {

    private final String dataStructureCellLabel;

    public CellDataStructure(String dataStructureCellLabel) {
        this.dataStructureCellLabel = dataStructureCellLabel;
    }

    public String dataStructureCellLabel() {
        return dataStructureCellLabel;
    }

}
