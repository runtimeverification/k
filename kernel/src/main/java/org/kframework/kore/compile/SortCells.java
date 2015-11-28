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

import javax.annotation.Nonnull;
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
import java.util.stream.Stream;

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
 * expression involving the split variables, using the cell fragment productions
 * introduced along with the cell labels.
 */
public class SortCells {
    private final ConcretizationInfo cfg;
    public SortCells(ConfigurationInfo cfgInfo, LabelInfo labelInfo) {
        this.cfg = new ConcretizationInfo(cfgInfo, labelInfo);
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

    // Information on uses of a particular cell fragment variable
    private class VarInfo {
        KVariable var;
        KLabel parentCell;
        LinkedHashSet<Sort> remainingCells;
        Map<Sort, K> split;

        void addOccurances(KLabel cell, KVariable var, List<K> items) {
            assert split == null; // need to add all occurances before getting any split.
            this.var = var;
            if (parentCell == null) {
                parentCell = cell;
            } else if (!parentCell.equals(cell)) {
                throw KEMException.criticalError("Cell variable "+var+" used under two cells, "
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
                } else if (item instanceof KVariable && !item.equals(var)) {
                    if (item.att().contains(Attribute.SORT_KEY)) {
                        Sort sort = Sort(item.att().<String>get(Attribute.SORT_KEY).get());
                        remainingCells.remove(sort);
                    }
                }
            }
        }

        K replacementTerm() {
            getSplit(var);
            KLabel fragmentLabel = cfg.getCellFragmentLabel(parentCell);
            if (fragmentLabel == null) {
                throw KEMException.compilerError("Unsupported cell fragment with types: " + remainingCells, var);
            }
            List<Sort> children = cfg.getChildren(parentCell);
            List<K> arguments = new ArrayList<>(children.size());
            for (Sort child : children) {
                K arg = split.get(child);
                if (arg == null) {
                    if (cfg.getMultiplicity(child) == Multiplicity.ONE) {
                        arg = cfg.getCellAbsentTerm(child);
                    } else {
                        arg = cfg.cfg.getUnit(child);
                    }
                }
                assert arg != null;
                arguments.add(arg);
            }
            return KApply(fragmentLabel, immutable(arguments));
        }

       Map<Sort, K> getSplit(KVariable var) {
            if(split != null) {
                return split;
            }
            if (remainingCells.size() == 0) {
                split = Collections.emptyMap();
            } else if (remainingCells.size() == 1) {
                Sort s = Iterables.getOnlyElement(remainingCells);
                split = ImmutableMap.of(s, KVariable(var.name(), var.att().remove(Attribute.SORT_KEY)));
            } else {
                split = new HashMap<>();
                for (Sort cell : remainingCells) {
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
    private Map<KVariable, Sort> cellVariables = new HashMap<>();
    private Set<KVariable> previousVars = new HashSet<>();

    private void resetVars() {
        variables.clear(); cellVariables.clear(); previousVars.clear(); counter = 0;
    }

    private void analyzeVars(K term) {
        new VisitKORE() {
            private boolean inRewrite = false;
            private boolean inRhs = false;

            private Stream<K> streamCells(K term) {
                return IncompleteCellUtils.flattenCells(term).stream();
            }

            private K left(K term) {
                if (term instanceof KRewrite) {
                    return ((KRewrite)term).left();
                } else {
                    return term;
                }
            }
            private K right(K term) {
                if (term instanceof KRewrite) {
                    return ((KRewrite)term).right();
                } else {
                    return term;
                }
            }

            @Override
            public Void apply(KApply k) {
                if (cfg.isParentCell(k.klabel())) {
                    if (inRewrite) {
                        processSide(k, inRhs, k.klist().stream()
                                .flatMap(this::streamCells)
                                .collect(Collectors.toList()));
                    } else {
                        processSide(k, false, k.klist().stream()
                                .flatMap(this::streamCells).map(this::left).flatMap(this::streamCells)
                                .collect(Collectors.toList()));

                        processSide(k, true, k.klist().stream()
                                .flatMap(this::streamCells).map(this::right).flatMap(this::streamCells)
                                .collect(Collectors.toList()));
                    }
                }
                return super.apply(k);
            }

            private void processSide(KApply parentCell, boolean allowRhs, List<K> items) {
                List<KVariable> bagVars = new ArrayList<>();
                for (K item : items) {
                    if (item instanceof KVariable) {
                        KVariable var = (KVariable) item;
                        if (var.att().contains(Attribute.SORT_KEY)) {
                            Sort sort = Sort(var.att().<String>get(Attribute.SORT_KEY).get());
                            if (cfg.cfg.isCell(sort)) {
                                if (!cellVariables.getOrDefault(var, sort).equals(sort)) {
                                    Sort prevSort = cellVariables.get(var);
                                    throw KEMException.compilerError("Variable "+var+" occurs annotated as multiple cell sorts, "+sort+" and "+prevSort,
                                            item);
                                }
                                if (variables.containsKey(var)) {
                                    throw KEMException.compilerError("Variable "+var+" occurs with cell sort "+sort+" after occurance without cell sort annotation");
                                }
                                cellVariables.put(var,sort);
                                continue;
                            } else {
                                if (cellVariables.containsKey(var)) {
                                    throw KEMException.compilerError("Variable "+var+" occurs annotated as non-cell sort "+sort+" after appearing as cell sort "+cellVariables.get(var),item);
                                }
                            }
                        }
                        if (cellVariables.containsKey(var)) {
                            throw KEMException.compilerError("Variable "+var+" occurs without sort annotation after appearing as cell sort "+cellVariables.get(var),item);
                        }
                        bagVars.add(var);
                    }
                }
                if (!allowRhs && bagVars.size() > 1) {
                    throw KEMException.compilerError(
                            "AC matching of multiple cell variables not yet supported. "
                                    + "encountered variables " + bagVars + " in cell " + parentCell.klabel(), parentCell);
                }
                for (KVariable var : bagVars) {
                    if (!variables.containsKey(var)) {
                        variables.put(var, new VarInfo());
                    }
                    variables.get(var).addOccurances(parentCell.klabel(), var, items);
                }
            }

            @Override
            public Void apply(KRewrite k) {
                assert !inRewrite;
                inRewrite = true;
                apply(k.left());
                inRhs = true;
                apply(k.right());
                inRhs = false;
                inRewrite = false;
                return null;
            }

            @Override
            public Void apply(KVariable k) {
                previousVars.add(k);
                return null;
            }
        }.apply(term);
    }

    private Sort getPredicateSort(Sort s) {
        if (cfg.getMultiplicity(s) == Multiplicity.STAR) {
            scala.collection.Set<Sort> sorts = cfg.cfg.getCellBagSortsOfCell(s);
            if (sorts.size() != 1) {
                throw KEMException.compilerError("Expected exactly one cell collection sort for the sort " + s + "; found " + sorts);
            }
            return stream(sorts).findFirst().get();
        }
        return s;
    }

    private boolean isCellFragmentTest(KApply app) {
        if (app.klist().size() != 1) return false;
        K argument = app.klist().items().get(0);
        if (!(argument instanceof KVariable)) return false;
        VarInfo info = variables.get((KVariable)argument);
        if (info == null) return false;
        KLabel expectedPredicate = KLabel("is"+cfg.getCellSort(info.parentCell).toString()+"Fragment");
        return app.klabel().equals(expectedPredicate);
    }

    /**
     * Expand away cell fragment variables, and correctly order the children of cells.
     * There are three significnat contexts for expanding cell fragments -
     * as an argument to a parent cell it splits into separate arguments for each of the variables
     * in most other uses, it expands into a term applying the appropriate {@code <cell>-fragment} label
     * to the split variables, except that applications of an {@code isCellFragment} sort predicate
     * to a cell fragment variable decomposes into a conjunction of sort predicate tests on the split
     * variables.
     */
    private K processVars(K term) {
        return new TransformKORE() {
            @Override
            public K apply(KApply k) {
                if (!cfg.isParentCell(k.klabel())) {
                    if (isCellFragmentTest(k)) {
                        return getSplit(k.klist().items().get(0)).entrySet().stream()
                                .map(e -> (K) KApply(KLabel("is" + getPredicateSort(e.getKey())), e.getValue()))
                                .reduce(BooleanUtils.TRUE, BooleanUtils::and);
                    } else if(k.klabel().name().equals("isBag")
                            && k.klist().size() == 1
                            && k.klist().items().get(0) instanceof KVariable) {
                        KVariable var = (KVariable)k.klist().items().get(0);
                        VarInfo info = variables.get(var);
                        if (info != null) {
                            return info.getSplit(var).entrySet().stream()
                                    .map(e -> (K) KApply(KLabel("is" + getPredicateSort(e.getKey())), e.getValue()))
                                    .reduce(BooleanUtils.TRUE, BooleanUtils::and);
                        }
                    }
                    return super.apply(k);
                } else {
                    List<Sort> order = cfg.getChildren(k.klabel());
                    ArrayList<K> ordered = new ArrayList<K>(Collections.nCopies(order.size(), null));
                    for (K item : k.klist().items()) {
                        Map<Sort, K> split = getSplit(item);
                        for (Map.Entry<Sort, K> e : split.entrySet()) {
                            int idx = order.indexOf(e.getKey());
                            if (ordered.get(idx) != null) {
                                ordered.set(idx, concatenateStarCells(e.getKey(), Arrays.asList(ordered.get(idx), e.getValue())));
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

            @Nonnull
            private Map<Sort, K> getSplit(K item) {
                if (item instanceof KVariable) {
                    VarInfo info = variables.get(item);
                    if (info == null) {
                        Sort cellSort = cellVariables.get(item);
                        if (cellSort == null) {
                            throw new IllegalArgumentException("Unknown variable " + item);
                        } else {
                            return ImmutableMap.of(cellSort,item);
                        }
                    }
                    return info.getSplit((KVariable) item);
                } else if (item instanceof KApply) {
                    List<K> children = IncompleteCellUtils.flattenCells(item);
                    if(children.size() == 1 && children.get(0) == item) {
                        final KLabel label = ((KApply) item).klabel();
                        Sort s = cfg.getCellSort(label);
                        if (s == null) {
                            s = cfg.getCellCollectionCell(label);
                            if (s == null) {
                                throw new IllegalArgumentException("Attempting to split non-cell term " + item);
                            }
                        }
                        return Collections.singletonMap(s, apply(item));
                    }
                    // flatten the List<Map<Sort, K>> into a Map<Sort, List<K>>
                    Map<Sort, List<K>> multiMap = children.stream().flatMap(e -> getSplit(e).entrySet().stream()).collect(
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
                    Map<Sort, K> splitLeft = new HashMap<>(getSplit(rw.left()));
                    Map<Sort, K> splitRight = new HashMap<>(getSplit(rw.right()));
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
                if (children.size() == 0) {
                    return cfg.cfg.getUnit(sort);
                }
                KLabel concat = cfg.cfg.getConcat(sort);
                int ix = children.size();
                K result = children.get(--ix);
                while (ix > 0) {
                    result = KApply(concat,children.get(--ix),result);
                }
                return result;
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
