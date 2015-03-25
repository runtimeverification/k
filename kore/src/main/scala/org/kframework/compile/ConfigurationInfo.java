// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.kore.KLabel;

/**
 * Created by brandon on 3/23/15.
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
