// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
import org.kframework.builtin.BooleanUtils;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfo.Multiplicity;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
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
    private final KExceptionManager kem;
    public SortCells(ConfigurationInfo cfgInfo, LabelInfo labelInfo, KExceptionManager kem) {
        this.cfg = new ConcretizationInfo(cfgInfo, labelInfo);
        this.kem = kem;
    }

    public synchronized K sortCells(K term) {
        resetVars();
        analyzeVars(term);
        return processVars(term);

    }

    private Rule sortCells(Rule rule) {
        resetVars();
        analyzeVars(rule.body());
        analyzeVars(rule.requires());
        analyzeVars(rule.ensures());
        return Rule(
                processVars(rule.body()),
                processVars(rule.requires()),
                processVars(rule.ensures()),
                rule.att());
    }

    private Context sortCells(Context context) {
        resetVars();
        analyzeVars(context.body());
        analyzeVars(context.requires());
        return new Context(
                processVars(context.body()),
                processVars(context.requires()),
                context.att());
    }

    public synchronized Sentence sortCells(Sentence s) {
        if (s instanceof Rule) {
            return sortCells((Rule) s);
        } else if (s instanceof Context) {
            return sortCells((Context) s);
        } else {
            return s;
        }
    }

    // Information on uses of a particular variable
    private class VarInfo {
        KVariable var;
        KLabel parentCell;
        LinkedHashSet<Sort> remainingCells;
        Map<Sort, K> split;

        void addOccurances(KLabel cell, KVariable var, List<K> items) {
            this.var = var;
            if (parentCell == null) {
                parentCell = cell;
            } else if (!parentCell.equals(cell)) {
                throw KEMException.criticalError("Cell variable used under two cells, "
                        + parentCell + " and " + cell);
            }
            if (remainingCells == null) {
                remainingCells = new LinkedHashSet<>(cfg.getChildren(cell));
            }
            if (var.att().contains(Attribute.SORT_KEY)) {
                Sort sort = Sort(var.att().<String>get(Attribute.SORT_KEY).get());
                if (cfg.cfg.isCell(sort)) {
                    remainingCells.removeIf(s -> !s.equals(sort));
                }
            }
            for (K item : items) {
                if (item instanceof KApply) {
                    KApply kApply = (KApply) item;
                    Sort s = cfg.getCellSort(kApply.klabel());
                    if (s != null && cfg.getMultiplicity(s) != Multiplicity.STAR) {
                        remainingCells.remove(s);
                    }
                } else if (item instanceof KVariable) {
                    if (item.att().contains(Attribute.SORT_KEY)) {
                        Sort sort = Sort(item.att().<String>get(Attribute.SORT_KEY).get());
                        remainingCells.remove(sort);
                    }
                }
            }
        }

        K replacementTerm() {
            if (remainingCells.size() == 1) {
                return KVariable(var.name(), var.att().remove(Attribute.SORT_KEY));
            }
            throw KEMException.compilerError("Unsupported cell fragment with types: " + remainingCells, var);
        }

        Map<Sort, K> getSplit(KVariable var) {
            return getSplit(var, false);
        }

        Sort getPredicateSort(Sort s) {
            if (cfg.getMultiplicity(s) == Multiplicity.STAR) {
                scala.collection.immutable.Set<Sort> sorts = cfg.cfg.getCellBagSortsOfCell(s);
                if (sorts.size() != 1) {
                    throw KEMException.compilerError("Expected exactly one cell collection sort for the sort " + s + "; found " + sorts);
                }
                return stream(sorts).findFirst().get();
            }
            return s;
        }


        Map<Sort, K> getSplit(KVariable var, boolean predicate) {
            if (remainingCells.size() == 0) {
                return Collections.emptyMap();
            }
            if (remainingCells.size() == 1) {
                Sort s = Iterables.getOnlyElement(remainingCells);
                if (predicate) {
                    return ImmutableMap.of(getPredicateSort(s), KVariable(var.name(), var.att().remove(Attribute.SORT_KEY)));
                }
                return ImmutableMap.of(s, KVariable(var.name(), var.att().remove(Attribute.SORT_KEY)));
            }
            if(split != null) {
                return split;
            }
            split = new HashMap<>();
            for (Sort cell : remainingCells) {
                if (predicate) {
                    split.put(getPredicateSort(cell), newDotVariable());
                } else {
                    split.put(cell, newDotVariable());
                }
            }
            return split;

        }
    }


    private int counter = 0;
    KVariable newDotVariable() {
        KVariable newLabel;
        do {
            newLabel = KVariable("_" + (counter++));
        } while (variables.containsKey(newLabel) || previousVars.contains(newLabel));
        variables.put(newLabel, null);
        return newLabel;
    }

    private Map<KVariable, VarInfo> variables = new HashMap<>();
    private Set<KVariable> previousVars = new HashSet<>();

    private void resetVars() {
        variables.clear(); previousVars.clear(); counter = 0;
    }

    private KRewrite rhsOf = null;

    private void analyzeVars(K term) {
        new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (cfg.isParentCell(k.klabel())) {
                    Map<KVariable, List<K>> leftVars = new HashMap<>();
                    Map<KVariable, List<K>> rightVars = new HashMap<>();
                    for (K item : k.klist().items()) {
                        prepareVarNeighbors(leftVars, item);
                        prepareVarNeighbors(rightVars, item);
                        if (item instanceof KRewrite) {
                            KRewrite rw = (KRewrite) item;
                            prepareVarNeighbors(leftVars, rw.left());
                            prepareVarNeighbors(rightVars, rw.right());
                        }
                    }
                    Set<KVariable> nonACVars = new HashSet<>();
                    for (KVariable var : leftVars.keySet()) {
                        if (var.att().contains(Attribute.SORT_KEY)) {
                            Sort sort = Sort(var.att().<String>get(Attribute.SORT_KEY).get());
                            if (cfg.cfg.isCell(sort))
                                nonACVars.add(var);
                        }
                    }
                    if (rhsOf == null && leftVars.size() - nonACVars.size() > 1) {
                        throw KEMException.compilerError(
                                "AC matching of multiple cell variables not yet supported. "
                                        + "encountered variables " + Sets.difference(leftVars.keySet(), nonACVars) + " in cell " + k, k);
                    }
                    for (K item : k.klist().items()) {
                        computeVarNeighbors(leftVars, rightVars, item);
                    }
                    for(Map.Entry<KVariable, List<K>> entry : rightVars.entrySet()) {
                        if (leftVars.containsKey(entry.getKey())) {
                            leftVars.get(entry.getKey()).addAll(entry.getValue());
                        } else {
                            leftVars.put(entry.getKey(), entry.getValue());
                        }
                    }
                    for (KVariable var : leftVars.keySet()) {
                        if (!variables.containsKey(var)) {
                            variables.put(var, new VarInfo());
                        }
                        variables.get(var).addOccurances(k.klabel(), var, leftVars.get(var));
                    }
                }
                return super.apply(k);
            }

            private void prepareVarNeighbors(Map<KVariable, List<K>> vars, K item) {
                if (item instanceof KVariable) {
                    vars.put((KVariable)item, new ArrayList<>());
                }
            }

            private void computeVarNeighbors(Map<KVariable, List<K>> leftVars, Map<KVariable, List<K>> rightVars, K item) {
                if (item instanceof KVariable) {
                    leftVars.entrySet().stream().filter(var -> !var.getKey().equals(item))
                            .forEach(e -> e.getValue().add(item));
                    rightVars.entrySet().stream().filter(var -> !var.getKey().equals(item))
                            .forEach(e -> e.getValue().add(item));
                } else if (item instanceof KRewrite) {
                    KRewrite rw = (KRewrite) item;
                    leftVars.entrySet().stream().forEach(e -> {
                        computeVarNeighbors(leftVars, Collections.emptyMap(), rw.left());
                    });
                    rightVars.entrySet().stream().forEach(e -> {
                        computeVarNeighbors(Collections.emptyMap(), rightVars, rw.right());
                    });
                } else {
                    leftVars.entrySet().stream().forEach(e -> e.getValue().add(item));
                    rightVars.entrySet().stream().forEach(e -> e.getValue().add(item));
                }
            }

            @Override
            public Void apply(KRewrite k) {
                apply(k.left());
                rhsOf = k;
                apply(k.right());
                rhsOf = null;
                return null;
            }

            @Override
            public Void apply(KVariable k) {
                previousVars.add(k);
                return null;
            }
        }.apply(term);
    }

    private K processVars(K term) {
        return new TransformKORE() {
            @Override
            public K apply(KApply k) {
                if (!cfg.isParentCell(k.klabel())) {
                    if (k.klabel().name().equals("isBag")) {
                        if (k.klist().size() != 1) {
                            throw KEMException.compilerError("Unexpected isBag predicate not of arity 1 found; cannot compile to sorted cells.", k);
                        }
                        K item = k.klist().items().get(0);
                        Map<Sort, K> split = getSplit(item, true);
                        if (split == null) {
                            kem.registerCompilerWarning("Unchecked isBag predicate found. Treating as isK.", k);
                            if (item instanceof KVariable) {
                                return KVariable(((KVariable) item).name(), item.att().remove(Attribute.SORT_KEY));
                            }
                            return BooleanUtils.TRUE;
                        }
                        return split.entrySet().stream().map(e -> (K)KApply(KLabel("is" + e.getKey()), e.getValue())).reduce(BooleanUtils.TRUE, BooleanUtils::and);
                    }
                    return super.apply(k);
                } else {
                    List<Sort> order = cfg.getChildren(k.klabel());
                    ArrayList<K> ordered = new ArrayList<K>(Collections.nCopies(order.size(), null));
                    for (K item : k.klist().items()) {
                        Map<Sort, K> split = getSplit(item, false);
                        assert split != null;
                        for (Map.Entry<Sort, K> e : split.entrySet()) {
                            int idx = order.indexOf(e.getKey());
                            if (ordered.get(idx) != null) {
                                ordered.set(idx, concatenateStarCells(e.getKey(), Arrays.asList(e.getValue(), ordered.get(idx))));
                            } else {
                                ordered.set(order.indexOf(e.getKey()), e.getValue());
                            }
                        }
                    }
                    order.stream().filter(s -> ordered.get(order.indexOf(s)) == null).forEach(sort -> {
                        if (cfg.getMultiplicity(sort) == Multiplicity.ONE) {
                            throw KEMException.compilerError("Missing cell of multiplicity=\"1\": " + sort, k);
                        } else {
                            ordered.set(order.indexOf(sort), cfg.cfg.getUnit(sort));
                        }
                    });
                    return KApply(k.klabel(), KList(ordered), k.att());
                }
            }

            private Map<Sort, K> getSplit(K item, boolean predicate) {
                if (item instanceof KVariable) {
                    VarInfo info = variables.get(item);
                    if (info == null) return null;
                    return info.getSplit((KVariable) item, predicate);
                } else if (item instanceof KApply) {
                    List<K> children = IncompleteCellUtils.flattenCells(item);
                    if(children.size() == 1 && children.get(0) == item) {
                        Sort s = cfg.getCellSort(((KApply) item).klabel());
                        if (s == null) return null;
                        return Collections.singletonMap(s, apply(item));
                    }
                    // flatten the List<Map<Sort, K>> into a Map<Sort, List<K>>
                    Map<Sort, List<K>> multiMap = children.stream().flatMap(e -> getSplit(e, predicate).entrySet().stream()).collect(
                            Collectors.groupingBy(Map.Entry::getKey,
                                    Collectors.mapping(Map.Entry::getValue, Collectors.toList())));
                    return multiMap.entrySet().stream().filter(e -> e.getValue().size() > 0).collect(Collectors.toMap(e -> e.getKey(), e -> {
                        if (e.getValue().size() == 1) {
                            return e.getValue().get(0);
                        } else {
                            return concatenateStarCells(e.getKey(), e.getValue());
                        }
                    }));
                } else if (item instanceof KRewrite) {
                    KRewrite rw = (KRewrite) item;
                    Map<Sort, K> splitLeft = new HashMap<>(getSplit(rw.left(), predicate));
                    Map<Sort, K> splitRight = new HashMap<>(getSplit(rw.right(), predicate));
                    addDefaultCells(item, splitLeft, splitRight);
                    addDefaultCells(item, splitRight, splitLeft);
                    assert splitLeft.keySet().equals(splitRight.keySet());
                    return splitLeft.keySet().stream().collect(Collectors.toMap(sort -> sort,
                            sort -> KRewrite(splitLeft.get(sort), splitRight.get(sort), rw.att())));
                } else {
                    throw KEMException.compilerError("Unexpected kind of term found in cell. Expected variable, "
                            + "apply, or rewrite; found " + item.getClass().getSimpleName(), item);
                }
            }

            private K concatenateStarCells(Sort sort, List<K> children) {
                if (cfg.getMultiplicity(sort) != Multiplicity.STAR) {
                    throw KEMException.compilerError("Attempting to concatenate cells not of multiplicity=\"*\" "
                            + "into a cell collection.", children.iterator().next());
                }
                return children.stream().reduce(cfg.cfg.getUnit(sort), (k1, k2) -> KApply(cfg.cfg.getConcat(sort), k1, k2));
            }

            private void addDefaultCells(K item, Map<Sort, K> splitLeft, Map<Sort, K> splitRight) {
                for (Sort s : Sets.difference(splitLeft.keySet(), splitRight.keySet())) {
                    if (cfg.getMultiplicity(s) == Multiplicity.ONE) {
                        throw KEMException.compilerError("Cannot rewrite a multiplicity=\"1\" cell to or from the cell unit.", item);
                    } else {
                        splitRight.put(s, cfg.cfg.getUnit(s));
                    }
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
