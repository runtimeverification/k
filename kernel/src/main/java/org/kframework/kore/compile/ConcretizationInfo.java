// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;

import java.util.List;

import static org.kframework.kore.KORE.*;

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


    public Sort getCellSort(K k) {
        if (k instanceof KApply) {
            return labels.getCodomain(((KApply) k).klabel());
        } else if (k instanceof KVariable) {
            return Sort(k.att().<String>get("sort").get());
        } else {
            throw new AssertionError("expected KApply or KVariable, found " + k.getClass().getSimpleName());
        }
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
        return getParent(labels.getCodomain(klabel));
    }

    public KLabel getParent(Sort sort) {
        return cfg.getCellLabel(cfg.getParent(sort));
    }

    public Sort getCellSort(KLabel cellLabel) {
        Sort s = labels.getCodomain(cellLabel);
        return cfg.isCell(s) ? s : null;
    }

    public boolean isCell(KLabel klabel) {
        Sort s = labels.getCodomain(klabel);
        return cfg.isCell(s) && cfg.getCellLabel(s).equals(klabel);
    }
    public boolean isLeafCell(KLabel klabel) {
        return cfg.isLeafCell(labels.getCodomain(klabel));
    }
    public boolean isParentCell(KLabel klabel) {
        return isCell(klabel) && cfg.isParentCell(labels.getCodomain(klabel));
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
