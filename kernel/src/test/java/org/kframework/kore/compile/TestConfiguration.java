// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Maps;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import scala.collection.immutable.Set;

import java.util.List;
import java.util.Map;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * Created by brandon on 3/24/15.
 */
class TestConfiguration implements ConfigurationInfo {

    Map<Sort, Integer> levels = Maps.newHashMap();
    Map<Sort, Sort> parents = Maps.newHashMap();
    Map<Sort, Sort> leafCellTypes = Maps.newHashMap();
    ListMultimap<Sort, Sort> children = ArrayListMultimap.create();
    Sort topCell = null;
    Sort computationCell = null;

    Map<Sort, Multiplicity> multiplicities = Maps.newHashMap();
    Map<Sort, K> defaultCells = Maps.newHashMap();
    Map<Sort, K> units = Maps.newHashMap();
    Map<Sort, KLabel> concats = Maps.newHashMap();
    Map<Sort, KLabel> cellLabels = Maps.newHashMap();

    public void addCell(String parent, String child, String label) {
        addCell(parent, child, label, Multiplicity.ONE);
    }
    public void addCell(String parent, String child, String label, Sort contents) {
        addCell(parent, child, label, Multiplicity.ONE, contents);
    }
    public void addCell(String parent, String child, String label, Multiplicity m) {
        addCell(parent, child, label, m, null);
    }
    public void addCell(String parent, String child, String label, Multiplicity m, Sort contents) {
        if (parent != null) {
            parents.put(Sort(child), Sort(parent));
            children.put(Sort(parent), Sort(child));
            levels.put(Sort(child), 1 + levels.get(Sort(parent)));
        } else {
            levels.put(Sort(child), 0);
        }
        if (contents != null) {
            leafCellTypes.put(Sort(child), contents);
        }
        multiplicities.put(Sort(child), m);
        cellLabels.put(Sort(child), KLabel(label));
    }

    public void addDefault(String cell, K term) {
        defaultCells.put(Sort(cell),term);
    }

    public void addUnit(String cell, K term) { units.put(Sort(cell), term); }

    public void addConcat(String cell, KLabel label) { concats.put(Sort(cell), label); }

    public TestConfiguration() {
    }

    @Override
    public int getLevel(Sort k) {
        return levels.getOrDefault(k, -1);
    }

    @Override
    public Sort getParent(Sort k) {
        return parents.get(k);
    }

    @Override
    public List<Sort> getChildren(Sort k) {
        return children.get(k);
    }

    @Override
    public Multiplicity getMultiplicity(Sort k) {
        return multiplicities.get(k);
    }

    @Override
    public boolean isCell(Sort k) {
        return levels.containsKey(k);
    }

    @Override
    public boolean isLeafCell(Sort k) {
        return !children.containsKey(k) && isCell(k);
    }

    @Override
    public boolean isParentCell(Sort k) {
        return children.containsKey(k);
    }

    @Override
    public Sort leafCellType(Sort k) {
        return leafCellTypes.get(k);
    }

    @Override
    public KLabel getCellLabel(Sort k) {
        return cellLabels.get(k);
    }

    @Override
    public K getDefaultCell(Sort k) {
        return defaultCells.get(k);
    }

    @Override
    public boolean isConstantInitializer(Sort k) {
        return true;
    }

    @Override
    public Sort getRootCell() {
        return topCell;
    }

    @Override
    public Sort getComputationCell() {
        return computationCell;
    }

    @Override
    public K getUnit(Sort k) { return units.get(k); }

    @Override
    public KLabel getConcat(Sort k) { return concats.get(k); }

    @Override
    public Set<Sort> getCellBagSortsOfCell(Sort k) {
        return Set(Sort(k.name() + "Bag"));
    }
}
