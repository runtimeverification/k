// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import java.util.List;

/**
 * Created by brandon on 3/31/15.
 */
public class ConcretizationInfo {
    public final ConfigurationInfo cfg;
    private final LabelInfo labels;

    public ConcretizationInfo(ConfigurationInfo cfg, LabelInfo labels) {
        this.cfg = cfg;
        this.labels = labels;
    }


    public ConfigurationInfo.Multiplicity getMultiplicity(KLabel label) {
        return cfg.getMultiplicity(labels.getCodomain(label));
    }
    public ConfigurationInfo.Multiplicity getMultiplicity(Sort sort) {
        return cfg.getMultiplicity(sort);
    }

    public int getLevel(KLabel label) {
        return cfg.getLevel(labels.getCodomain(label));
    }

    public KLabel getParent(KLabel klabel) {
        return cfg.getCellLabel(cfg.getParent(labels.getCodomain(klabel)));
    }

    public Sort getCellSort(KLabel cellLabel) {
        Sort s = labels.getCodomain(cellLabel);
        return cfg.isCell(s) ? s : null;
    }

    public boolean isCell(KLabel klabel) {
        return cfg.isCell(labels.getCodomain(klabel));
    }
    public boolean isLeafCell(KLabel klabel) {
        return cfg.isLeafCell(labels.getCodomain(klabel));
    }
    public boolean isParentCell(KLabel klabel) {
        return cfg.isParentCell(labels.getCodomain(klabel));
    }

    public Sort leafCellType(KLabel label) {
        return cfg.leafCellType(labels.getCodomain(label));
    }
    public List<Sort> getChildren(KLabel label) {
        return cfg.getChildren(labels.getCodomain(label));
    }

    public K getDefaultCell(Sort sort) {
        return cfg.getDefaultCell(sort);
    }
}
