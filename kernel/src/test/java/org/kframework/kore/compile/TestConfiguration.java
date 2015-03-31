// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.ListMultimap;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import static org.kframework.kore.KORE.*;

import java.util.List;
import java.util.Map;

/**
 * Created by brandon on 3/24/15.
 */
class TestConfiguration implements ConfigurationInfo {

    Map<KLabel, Integer> levels = Maps.newHashMap();
    Map<KLabel, KLabel> parents = Maps.newHashMap();
    Map<KLabel, Sort> leafCellTypes = Maps.newHashMap();
    ListMultimap<KLabel, KLabel> children = ArrayListMultimap.create();

    Map<KLabel, Multiplicity> multiplicities = Maps.newHashMap();
    Map<KLabel, K> defaultCells = Maps.newHashMap();

    public void addCell(String parent, String child) {
        addCell(parent, child, Multiplicity.ONE);
    }
    public void addCell(String parent, String child, Sort contents) {
        addCell(parent, child, Multiplicity.ONE, contents);
    }
    public void addCell(String parent, String child, Multiplicity m) {
        addCell(parent, child, m, null);
    }
    public void addCell(String parent, String child, Multiplicity m, Sort contents) {
        if (parent != null) {
            parents.put(KLabel(child), KLabel(parent));
            children.put(KLabel(parent), KLabel(child));
            levels.put(KLabel(child), 1 + levels.get(KLabel(parent)));
        } else {
            levels.put(KLabel(child), 0);
        }
        if (contents != null) {
            leafCellTypes.put(KLabel(child), contents);
        }
        multiplicities.put(KLabel(child), m);
    }

    public void addDefault(String cell, K term) {
        defaultCells.put(KLabel(cell),term);
    }

    public TestConfiguration() {
    }

    @Override
    public int getLevel(KLabel k) {
        return levels.getOrDefault(k, -1);
    }

    @Override
    public KLabel getParent(KLabel k) {
        return parents.get(k);
    }

    @Override
    public List<KLabel> getChildren(KLabel k) {
        return children.get(k);
    }

    @Override
    public Multiplicity getMultiplicity(KLabel k) {
        return multiplicities.get(k);
    }

    @Override
    public boolean isCell(KLabel k) {
        return levels.containsKey(k);
    }

    @Override
    public boolean isLeafCell(KLabel k) {
        return !children.containsKey(k) && isCell(k);
    }

    @Override
    public boolean isParentCell(KLabel k) {
        return children.containsKey(k);
    }

    @Override
    public Sort leafCellType(KLabel k) {
        return leafCellTypes.get(k);
    }

    @Override
    public K getDefaultCell(KLabel k) {
        return defaultCells.get(k);
    }
}
