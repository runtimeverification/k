// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Maps;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import scala.Option;

import java.util.List;
import java.util.Map;
import java.util.Set;

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
    BiMap<Sort, KLabel> units = HashBiMap.create();
    BiMap<Sort, KLabel> concats = HashBiMap.create();
    Map<Sort, KLabel> cellLabels = Maps.newHashMap();
    Map<Sort, KLabel> cellFragmentLabels = Maps.newHashMap();
    Map<Sort, KLabel> cellAbsentLabels = Maps.newHashMap();
    Map<Sort, Sort> cellCollectionSorts = Maps.newHashMap();

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
            if (!children.containsKey(Sort(parent))) {
                // create a fragment label for the parent cell.
                cellFragmentLabels.put(Sort(parent),KLabel(cellLabels.get(Sort(parent)).name()+"-fragment"));
            }
            if (m != Multiplicity.STAR) {
                cellAbsentLabels.put(Sort(child),KLabel("no"+child));
            }
            if (m == Multiplicity.STAR) {
                cellCollectionSorts.put(Sort(child+"Bag"),Sort(child));
            }
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
        defaultCells.put(Sort(cell), term);
    }

    public void addUnit(String cell, KLabel label) { units.put(Sort(cell), label); }

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
    public boolean isCellCollection(Sort s) {
        return cellCollectionSorts.containsKey(s);
    }

    @Override
    public boolean isCellLabel(KLabel kLabel) {
        return getCellSort(kLabel) != null;
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
    public Sort getCellSort(KLabel kLabel) {
        if (kLabel != null) {
            return cellLabels.entrySet().stream().filter(e -> kLabel.equals(e.getValue())).map(Map.Entry::getKey).findAny().orElseGet(null);
        } else {
            return null;
        }
    }

    @Override
    public KLabel getCellFragmentLabel(Sort k) { return cellFragmentLabels.get(k); }

    @Override
    public KLabel getCellAbsentLabel(Sort k) { return cellAbsentLabels.get(k); }

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
    public Set<Sort> getCellSorts() {
        return cellLabels.keySet();
    }

    @Override
    public KApply getUnit(Sort k) { return KApply(units.get(k)); }

    @Override
    public KLabel getConcat(Sort k) { return concats.get(k); }

    @Override
    public Option<Sort> getCellForConcat(KLabel concat) {
        return Option.apply(concats.inverse().get(concat));
    }

    @Override
    public Option<Sort> getCellForUnit(KLabel unit) {
        return Option.apply(units.inverse().get(unit));
    }

    @Override
    public scala.collection.Set<Sort> getCellBagSortsOfCell(Sort k) {
        return Set(Sort(k.name() + "Bag"));
    }
}
