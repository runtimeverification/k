// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

/**
 * Information about the configuration structure used
 * in the configuration concretiziation passes.
 */
import java.util.Collection;

public interface ConfigurationInfo {
    int getLevel(KLabel k);

    KLabel getParent(KLabel k);
    Collection<KLabel> getChildren(KLabel k);

    Multiplicity getMultiplicity(KLabel k);

    boolean isCell(KLabel k);

    boolean isLeafCell(KLabel k);

    boolean isParentCell(KLabel k);

    Sort leafCellType(KLabel k);

    K getDefaultCell(KLabel k);

    public enum Multiplicity {ONE, OPTIONAL, STAR}
}
