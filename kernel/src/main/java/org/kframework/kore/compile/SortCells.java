// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.*;
import java.util.Collections;

import static org.kframework.kore.KORE.*;

/**
 * Arrange cell contents and variables to match the klabels declared for cells.
 * In Full K, cell contents can be written in any order, and variables can
 * be written that match multiple cells.
 * <p/>
 * In the input to this pass, parent cells are represented by appling the label directly
 * to a klist of all the children, variables, and rewrites under the cell.
 * Left cells should already be in their final form.
 * In the output each cell will be represented by using the cell labels in agreement
 * with the production declaring it, so parent cells will have a fixed arity with separate
 * argument positions reserved for different types of child cell.
 * <p/>
 * The most complicated part of the transformation is dealing with variables
 * in cells. An occurrence in a cell that might match child cells of different
 * sorts has to be split into several variables in different arguments, and any
 * occurrence of the variable outside of a cell replaced by a suitable
 * expression involving the split variables.
 * <p/>
 * This is currently not implemented in general, just the analysis to identify
 * the simple cases where there is in fact only one or zero (types of) cells
 * that a variable can bind, so it can be handled by either doing nothing,
 * or just deleting it from under cells and replacing it with an empty collection elsewhere.
 */
// TODO handle cell rewrites
public class SortCells {
    private final ConcretizationInfo cfg;

    public SortCells(ConfigurationInfo cfgInfo, LabelInfo labelInfo) {
        this.cfg = new ConcretizationInfo(cfgInfo, labelInfo);
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
                        + parentCell + " and " + cell);
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

    protected void resetVars() {
        variables.clear();
    }

    protected void analyzeVars(K term) {
        new VisitKORE() {
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
                                                + "encountered variables " + var.toString() + " and "
                                                + item.toString() + " in cell " + k);
                            } else {
                                var = (KVariable) item;
                            }
                        } else {
                            items.add(item);
                        }
                    }
                    if (var != null) {
                        if (!variables.containsKey(var)) {
                            variables.put(var, new VarInfo());
                        }
                        variables.get(var).addOccurances(cfg, k.klabel(), var, items);
                    }
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    private K processVars(K term) {
        return new TransformKORE() {
            @Override
            public K apply(KApply k) {
                if (!cfg.isParentCell(k.klabel())) {
                    return super.apply(k);
                } else {
                    List<Sort> order = cfg.getChildren(k.klabel());
                    ArrayList<K> ordered = new ArrayList<K>(Collections.nCopies(order.size(), null));
                    for (K item : k.klist().items()) {
                        if (item instanceof KVariable) {
                            VarInfo info = variables.get(item);
                            Map<Sort, K> split = info.getSplit((KVariable) item);
                            for (Map.Entry<Sort, K> e : split.entrySet()) {
                                ordered.set(order.indexOf(e.getKey()), e.getValue());
                            }
                        } else if (item instanceof KApply) {
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

    public K sortCells(K term) {
        resetVars();
        analyzeVars(term);
        return processVars(term);

    }


    public Rule sortCells(Rule rule) {
        resetVars();
        analyzeVars(rule.body());
        analyzeVars(rule.requires());
        analyzeVars(rule.ensures());
        return new Rule(
                processVars(rule.body()),
                processVars(rule.requires()),
                processVars(rule.ensures()),
                rule.att());
    }

    public Context sortCells(Context context) {
        resetVars();
        analyzeVars(context.body());
        analyzeVars(context.requires());
        return new Context(
                processVars(context.body()),
                processVars(context.requires()),
                context.att());
    }

    public Sentence sortCells(Sentence s) {
        if (s instanceof Rule) {
            return sortCells((Rule) s);
        } else if (s instanceof Context) {
            return sortCells((Context) s);
        } else {
            return s;
        }
    }

    ModuleTransformer moduleTransormer = ModuleTransformer.from(this::sortCells);

    public Module sortCells(Module m) {
        return moduleTransormer.apply(m);
    }
}
