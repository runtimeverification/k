// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.kore.KLabel;

/**
 * Information about the configuration structure used
 * in the configuration concretiziation passes.
 */
public interface ConfigurationInfo {
    int getLevel(KLabel k);

    KLabel getParent(KLabel k);

    Multiplicity getMultiplicity(KLabel k);

    boolean isCell(KLabel k);

    boolean isLeafCell(KLabel k);

    boolean isParentCell(KLabel k);

    public enum Multiplicity {ONE, OPTIONAL, STAR}
}
