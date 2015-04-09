// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

/**
 * Information about the configuration structure used
 * in the configuration concretiziation passes.
 */
import java.util.List;

public interface ConfigurationInfo {
    int getLevel(Sort k);

    Sort getParent(Sort k);
    List<Sort> getChildren(Sort k);

    Multiplicity getMultiplicity(Sort k);

    boolean isCell(Sort k);

    boolean isLeafCell(Sort k);

    boolean isParentCell(Sort k);

    Sort leafCellType(Sort k);

    KLabel getCellLabel(Sort k);

    K getDefaultCell(Sort k);

    Sort getRootCell();
    Sort getComputationCell();

    enum Multiplicity {ONE, OPTIONAL, STAR}
}
