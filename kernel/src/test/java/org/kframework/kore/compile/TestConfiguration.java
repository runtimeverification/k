// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import static org.kframework.kore.KORE.*;

import java.util.Map;

/**
 * Created by brandon on 3/24/15.
 */
class TestConfiguration implements ConfigurationInfo {

    Map<KLabel, Integer> levels = Maps.newHashMap();
    Map<KLabel, KLabel> parents = Maps.newHashMap();
    Multimap<KLabel, KLabel> children = HashMultimap.create();

    Map<KLabel, Multiplicity> multiplicities = Maps.newHashMap();

    public void addCell(String parent, String child) {
        addCell(parent, child, Multiplicity.ONE);
    }
    public void addCell(String parent, String child, Multiplicity m) {
        if (parent != null) {
            parents.put(KLabel(child), KLabel(parent));
            children.put(KLabel(parent), KLabel(child));
            levels.put(KLabel(child), 1 + levels.get(KLabel(parent)));
        } else {
            levels.put(KLabel(child), 0);
        }
        multiplicities.put(KLabel(child), m);
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
}
