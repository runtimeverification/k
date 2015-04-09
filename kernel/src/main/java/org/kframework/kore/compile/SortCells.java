// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.kore.*;

import java.util.*;

import static org.kframework.kore.KORE.*;

/**
 * Arrange cell contents and variables to match the klabels declared for cells.
 * In Full K, cell contents can be written in any order, and variables can
 * be written that match multiple cells.
 *
 * In the input to this pass, cells are represented by applying the corresponding
 * label to a single argument which is an unordered bag of cells,
 * in the output each cell label will be applied to arguments matching the
 * production declaring it.
 *
 * The most complicated part of the transformation is dealing with variables
 * in cells. An occurance in a cell that might match child cells of different
 * sorts has to be split into several variables in different arguments, and any
 * occurance of the variable outside of a cell replaced by a suitable
 * expression involving the split variables.
 *
 * This is currently not implemented in general, just the analysis to identify
 * the simple cases where there is in fact only one or zero (types of) cells
 * that a variable can bind, so it can be handled by either doing nothing,
 * or just deleting it from under cells and replacing it with an empty collection elsewhere.
 */
public class SortCells {
    private final ConcretizationInfo cfg;

    public SortCells(ConcretizationInfo cfg) {
        this.cfg = cfg;
    }

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

    private Map<KVariable, VarInfo> variables = new HashMap<>();

    public K sortCells(K term) {
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
}
