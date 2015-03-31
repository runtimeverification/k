// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.kore.*;

import java.util.*;

import static org.kframework.kore.KORE.*;

/**
 * Rearrange partially-completed cells to follow the productions declaring them.
 *
 * The main complexity here is eliminating cell fragment variables that might
 * capture multiple cells. In the general case a variable needs to be
 * replaced under cells with separate variables in several slots of the
 * parent and in other places with an appropriate bag expression.
 */
public class SortCellsTest {
    // Information on uses of a particular variable
    static class VarInfo {
        KVariable var;
        KLabel parentCell;
        Set<Sort> remainingCells;

        void addOccurances(ConcretizationInfo cfg, KLabel cell, KVariable var, List<K> items) {
            this.var = var;
            if (parentCell == null) {
                parentCell = cell;
            } else if (!parentCell.equals(cell)) {
                throw new IllegalArgumentException("Cell variable used under two cells, "
                +parentCell+" and "+cell);
            }
            if (remainingCells == null) {
                remainingCells = new HashSet<>(cfg.getChildren(cell));
            }
            for (K item : items) {
                if (item instanceof KApply) {
                    KApply kApply = (KApply) item;
                    Sort s = cfg.getCellSort(kApply.klabel());
                    if (cfg.getMultiplicity(s) != ConfigurationInfo.Multiplicity.STAR) {
                        remainingCells.remove(s);
                    }
                }
            }
        }

        K replacementTerm() {
            if (remainingCells.size() == 1) {
                return var;
            }
            assert false;
            return null;
        }

        Map<Sort, K> getSplit(KVariable var) {
            if (remainingCells.size() == 0) {
                return Collections.emptyMap();
            }
            if (remainingCells.size() == 1) {
                return ImmutableMap.of(Iterables.getOnlyElement(remainingCells), var);
            }
            assert false;
            return null;
        }
    }

    Map<KVariable, VarInfo> variables = new HashMap<>();

    ConfigurationInfo cfgInfo = new TestConfiguration() {{
        addCell(null, "TopCell", "<top>");
        addCell("TopCell", "ThreadCell", "<t>");
        addCell("ThreadCell", "KCell", "<k>", Sort("K"));
        addCell("ThreadCell", "EnvCell", "<env>", Sort("Map"));
    }};
    LabelInfo labelInfo = new LabelInfo() {{
        addLabel("TopCell", "<top>");
        addLabel("ThreadCell", "<t>");
        addLabel("KCell", "<k>");
        addLabel("EnvCell", "<env>");
    }};
    ConcretizationInfo cfg = new ConcretizationInfo(cfgInfo, labelInfo);

    K sortCells(K term) {
        new VisitKORE(){
            @Override
            public Void apply(KApply k) {
                if (cfg.isParentCell(k.klabel())) {
                    KVariable var = null;
                    List<K> items = new ArrayList<>(k.klist().size());
                    for (K item : k.klist().items()) {
                        if (item instanceof KVariable) {
                            if (var != null) {
                                throw new UnsupportedOperationException(
                                        "AC matching of multiple cell variables not yet supported. "
                                        +"encountered variables "+var.toString()+" and "
                                        +item.toString()+" in cell "+k);
                            } else {
                                var = (KVariable)item;
                            }
                        } else {
                            items.add(item);
                        }
                    }
                    if (var != null) {
                        if (!variables.containsKey(var)) {
                            variables.put(var,new VarInfo());
                        }
                        variables.get(var).addOccurances(cfg, k.klabel(), var, items);
                    }
                }
                return super.apply(k);
            }
        }.apply(term);

        return new TransformKORE(){
            @Override
            public K apply(KApply k) {
                if (!cfg.isCell(k.klabel())) {
                    return super.apply(k);
                } else {
                    List<Sort> order = cfg.getChildren(k.klabel());
                    ArrayList<K> ordered = new ArrayList<K>(Collections.nCopies(order.size(), null));
                    for (K item : k.klist().items()) {
                        if (item instanceof KVariable) {
                            VarInfo info = variables.get(item);
                            Map<Sort, K> split = info.getSplit((KVariable)item);
                            for (Map.Entry<Sort,K> e : split.entrySet()) {
                                ordered.set(order.indexOf(e.getKey()), e.getValue());
                            }
                        } else if (item instanceof KApply){
                            ordered.set(order.indexOf(cfg.getCellSort(((KApply) item).klabel())), apply(item));
                        } else {
                            assert false;
                        }
                    }
                    return KApply(k.klabel(), KList(ordered), k.att());
                }
            }
            @Override
            public K apply(KVariable v) {
                VarInfo info = variables.get(v);
                if (info != null) {
                    return info.replacementTerm();
                } else {
                    return v;
                }
            }
        }.apply(term);
    }

    @Test
    public void testSimpleSplitting() {
        K term = KRewrite(cell("<t>",cell("<env>"),KVariable("X")),KVariable("X"));
        K expected = KRewrite(cell("<t>",KVariable("X"),cell("<env>")),KVariable("X"));
        Assert.assertEquals(expected, sortCells(term));
    }

    @Test
    public void testUselessVariable() {
        K term = cell("<t>",cell("<env>"),cell("<k>"),KVariable("X"));
        K expected = cell("<t>",cell("<k>"),cell("<env>"));
        Assert.assertEquals(expected, sortCells(term));
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
