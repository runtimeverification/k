// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Iterables;
import com.google.common.collect.Sets;
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
import javax.annotation.Nonnull;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo.Multiplicity;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;
import scala.collection.JavaConversions;

/**
 * Arrange cell contents and variables to match the klabels declared for cells. In Full K, cell
 * contents can be written in any order, and variables can be written that match multiple cells.
 *
 * <p>In the input to this pass, parent cells are represented by appling the label directly to a
 * klist of all the children, variables, and rewrites under the cell. Left cells should already be
 * in their final form. In the output each cell will be represented by using the cell labels in
 * agreement with the production declaring it, so parent cells will have a fixed arity with separate
 * argument positions reserved for different types of child cell.
 *
 * <p>The most complicated part of the transformation is dealing with variables in cells. An
 * occurrence in a cell that might match child cells of different sorts has to be split into several
 * variables in different arguments, and any occurrence of the variable outside of a cell replaced
 * by a suitable expression involving the split variables, using the cell fragment productions
 * introduced along with the cell labels.
 */
public class SortCells {
  private final ConcretizationInfo cfg;
  private final LabelInfo labelInfo;
  private final Module module;

  public SortCells(ConfigurationInfo cfgInfo, LabelInfo labelInfo, Module module) {
    this.cfg = new ConcretizationInfo(cfgInfo, labelInfo);
    this.labelInfo = labelInfo;
    this.module = module;
  }

  public SortCells(ConfigurationInfo cfgInfo, LabelInfo labelInfo) {
    this.cfg = new ConcretizationInfo(cfgInfo, labelInfo);
    this.labelInfo = labelInfo;
    this.module = null;
  }

  public synchronized K sortCells(K term) {
    resetVars();
    analyzeVars(term);
    return processVars(term);
  }

  private RuleOrClaim sortCells(RuleOrClaim rule) {
    resetVars();
    analyzeVars(rule.body());
    analyzeVars(rule.requires());
    analyzeVars(rule.ensures());
    rule =
        rule.newInstance(
            processVars(rule.body()),
            processVars(rule.requires()),
            processVars(rule.ensures()),
            rule.att());
    rule =
        rule.newInstance(
            resolveIncompleteCellFragment(rule.body()),
            resolveIncompleteCellFragment(rule.requires()),
            resolveIncompleteCellFragment(rule.ensures()),
            rule.att());
    return rule;
  }

  private Context sortCells(Context context) {
    resetVars();
    analyzeVars(context.body());
    analyzeVars(context.requires());
    return new Context(processVars(context.body()), processVars(context.requires()), context.att());
  }

  public synchronized Sentence sortCells(Sentence s) {
    if (s instanceof RuleOrClaim) {
      return sortCells((RuleOrClaim) s);
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
        throw KEMException.criticalError(
            "Cell variable " + var + " used under two cells, " + parentCell + " and " + cell);
      }
      if (remainingCells == null) {
        remainingCells = new LinkedHashSet<>(cfg.getChildren(cell));
      }
      if (var.att().contains(Att.SORT(), Sort.class)) {
        Sort sort = var.att().get(Att.SORT(), Sort.class);
        if (cfg.cfg().isCell(sort)) {
          remainingCells.removeIf(s -> !s.equals(sort));
        }
      }
      for (K item : items) {
        if (item instanceof KApply kApply) {
          Sort s = cfg.getCellSort(kApply.klabel());
          if (s != null && cfg.getMultiplicity(s) != Multiplicity.STAR) {
            remainingCells.remove(s);
          }
        } else if (item instanceof KVariable && !item.equals(var)) {
          if (item.att().contains(Att.SORT(), Sort.class)) {
            Sort sort = item.att().get(Att.SORT(), Sort.class);
            remainingCells.remove(sort);
          }
        }
      }
    }

    K replacementTerm() {
      getSplit(var);
      KLabel fragmentLabel = cfg.getCellFragmentLabel(parentCell);
      if (fragmentLabel == null) {
        throw KEMException.compilerError(
            "Unsupported cell fragment with types: " + remainingCells, var);
      }
      List<Sort> children = cfg.getChildren(parentCell);
      List<K> arguments = new ArrayList<>(children.size());
      for (Sort child : children) {
        K arg = split.get(child);
        if (arg == null) {
          if (cfg.getMultiplicity(child) == Multiplicity.ONE) {
            arg = cfg.getCellAbsentTerm(child);
          } else {
            arg = cfg.cfg().getUnit(child);
          }
        }
        assert arg != null;
        arguments.add(arg);
      }
      return KApply(fragmentLabel, immutable(arguments));
    }

    Map<Sort, K> getSplit(KVariable var) {
      if (split != null) {
        return split;
      }
      if (remainingCells.size() == 0) {
        split = Collections.emptyMap();
      } else if (remainingCells.size() == 1) {
        Sort s = Iterables.getOnlyElement(remainingCells);
        if (cfg.getMultiplicity(s) == Multiplicity.STAR) {
          split =
              ImmutableMap.of(
                  s,
                  KVariable(
                      var.name(), var.att().add(Att.SORT(), Sort.class, getPredicateSort(s))));
        } else {
          split =
              ImmutableMap.of(
                  s,
                  KVariable(
                      var.name(), var.att().add(Att.SORT(), Sort.class, s).add(Att.CELL_SORT())));
        }
      } else {
        split = new HashMap<>();
        for (Sort cell : remainingCells) {
          split.put(
              cell,
              newDotVariable(var.att().add(Att.SORT(), Sort.class, cell).add(Att.CELL_SORT())));
        }
      }
      return split;
    }
  }

  private int counter = 0;

  KVariable newDotVariable(Att att) {
    KVariable newLabel;
    do {
      newLabel = KVariable("_Gen" + (counter++), att);
    } while (variables.containsKey(newLabel) || previousVars.contains(newLabel));
    variables.put(newLabel, null);
    return newLabel;
  }

  private final Map<KVariable, VarInfo> variables = new HashMap<>();
  private final Map<KVariable, Sort> cellVariables = new HashMap<>();
  private final Set<KVariable> previousVars = new HashSet<>();

  private void resetVars() {
    variables.clear();
    cellVariables.clear();
    previousVars.clear();
    counter = 0;
  }

  private void analyzeVars(K term) {
    new VisitK() {
      private boolean inRewrite = false;
      private boolean inRhs = false;

      private Stream<K> streamCells(K term) {
        return IncompleteCellUtils.flattenCells(term).stream();
      }

      private K left(K term) {
        if (term instanceof KRewrite) {
          return ((KRewrite) term).left();
        } else {
          return term;
        }
      }

      private K right(K term) {
        if (term instanceof KRewrite) {
          return ((KRewrite) term).right();
        } else {
          return term;
        }
      }

      @Override
      public void apply(KApply k) {
        if (cfg.isParentCell(k.klabel())) {
          if (inRewrite) {
            processSide(
                k,
                inRhs,
                k.klist().stream().flatMap(this::streamCells).collect(Collectors.toList()));
          } else {
            processSide(
                k,
                false,
                k.klist().stream()
                    .flatMap(this::streamCells)
                    .map(this::left)
                    .flatMap(this::streamCells)
                    .collect(Collectors.toList()));

            processSide(
                k,
                true,
                k.klist().stream()
                    .flatMap(this::streamCells)
                    .map(this::right)
                    .flatMap(this::streamCells)
                    .collect(Collectors.toList()));
          }
        }
        super.apply(k);
      }

      private void processSide(KApply parentCell, boolean allowRhs, List<K> items) {
        List<KVariable> bagVars = new ArrayList<>();
        for (K item : items) {
          if (item instanceof KVariable var) {
            if (var.att().contains(Att.SORT(), Sort.class)) {
              Sort sort = var.att().get(Att.SORT(), Sort.class);
              if (cfg.cfg().isCell(sort)) {
                if (!cellVariables.getOrDefault(var, sort).equals(sort)) {
                  Sort prevSort = cellVariables.get(var);
                  throw KEMException.compilerError(
                      "Variable "
                          + var
                          + " occurs annotated as multiple cell sorts, "
                          + sort
                          + " and "
                          + prevSort,
                      item);
                }
                if (variables.containsKey(var)) {
                  throw KEMException.compilerError(
                      "Variable "
                          + var
                          + " occurs with cell sort "
                          + sort
                          + " after occurance without cell sort annotation");
                }
                cellVariables.put(var, sort);
                continue;
              } else {
                if (cellVariables.containsKey(var)) {
                  throw KEMException.compilerError(
                      "Variable "
                          + var
                          + " occurs annotated as non-cell sort "
                          + sort
                          + " after appearing as cell sort "
                          + cellVariables.get(var),
                      item);
                }
              }
            }
            if (cellVariables.containsKey(var)) {
              throw KEMException.compilerError(
                  "Variable "
                      + var
                      + " occurs without sort annotation after appearing as cell sort "
                      + cellVariables.get(var),
                  item);
            }
            bagVars.add(var);
          }
        }
        if (!allowRhs && bagVars.size() > 1) {
          throw KEMException.compilerError(
              "AC matching of multiple cell variables not yet supported. "
                  + "encountered variables "
                  + bagVars
                  + " in cell "
                  + parentCell.klabel(),
              parentCell);
        }
        for (KVariable var : bagVars) {
          if (!variables.containsKey(var)) {
            variables.put(var, new VarInfo());
          }
          variables.get(var).addOccurances(parentCell.klabel(), var, items);
        }
      }

      @Override
      public void apply(KRewrite k) {
        assert !inRewrite;
        inRewrite = true;
        apply(k.left());
        inRhs = true;
        apply(k.right());
        inRhs = false;
        inRewrite = false;
      }

      @Override
      public void apply(KVariable k) {
        previousVars.add(k);
      }
    }.apply(term);
  }

  private Sort getPredicateSort(Sort s) {
    if (cfg.getMultiplicity(s) == Multiplicity.STAR) {
      scala.collection.Set<Sort> sorts = cfg.cfg().getCellBagSortsOfCell(s);
      if (sorts.size() != 1) {
        throw KEMException.compilerError(
            "Expected exactly one cell collection sort for the sort " + s + "; found " + sorts);
      }
      return stream(sorts).findFirst().get();
    }
    return s;
  }

  private boolean isCellFragmentTest(KApply app) {
    if (app.klist().size() != 1) return false;
    K argument = app.klist().items().get(0);
    if (!(argument instanceof KVariable)) return false;
    VarInfo info = variables.get((KVariable) argument);
    if (info == null) return false;
    KLabel expectedPredicate =
        KLabel("is" + cfg.getCellSort(info.parentCell).toString() + "Fragment");
    return app.klabel().equals(expectedPredicate);
  }

  private int indexOf(List<Sort> l, Sort o, KApply loc) {
    int idx = l.indexOf(o);
    if (idx == -1) {
      throw KEMException.compilerError(
          "Expected to find sort "
              + o.toString()
              + " in the children of cell with klabel "
              + loc.klabel(),
          loc);
    }
    return idx;
  }

  /**
   * Expand away cell fragment variables, and correctly order the children of cells. There are three
   * significnat contexts for expanding cell fragments - as an argument to a parent cell it splits
   * into separate arguments for each of the variables in most other uses, it expands into a term
   * applying the appropriate {@code <cell>-fragment} label to the split variables, except that
   * applications of an {@code isCellFragment} sort predicate to a cell fragment variable decomposes
   * into a conjunction of sort predicate tests on the split variables.
   */
  private K processVars(K term) {
    return new TransformK() {
      @Override
      public K apply(KApply k) {
        if (!cfg.isParentCell(k.klabel())) {
          if (isCellFragmentTest(k)) {
            return getSplit(k.klist().items().get(0)).entrySet().stream()
                .map(e -> (K) KApply(KLabel("is" + getPredicateSort(e.getKey())), e.getValue()))
                .reduce(BooleanUtils.TRUE, BooleanUtils::and);
          } else if (k.klabel().name().equals("isBag")
              && k.klist().size() == 1
              && k.klist().items().get(0) instanceof KVariable var) {
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
              int idx = indexOf(order, e.getKey(), k);
              if (ordered.get(idx) != null) {
                ordered.set(
                    idx,
                    concatenateStarCells(
                        e.getKey(), Arrays.asList(ordered.get(idx), e.getValue())));
              } else {
                ordered.set(idx, e.getValue());
              }
            }
          }
          order.stream()
              .filter(s -> ordered.get(indexOf(order, s, k)) == null)
              .forEach(
                  sort -> {
                    if (cfg.getMultiplicity(sort) == Multiplicity.ONE) {
                      throw KEMException.compilerError(
                          "Missing cell of multiplicity=\"1\": " + sort, k);
                    } else {
                      ordered.set(indexOf(order, sort, k), cfg.cfg().getUnit(sort));
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
              return ImmutableMap.of(cellSort, item);
            }
          }
          return info.getSplit((KVariable) item);
        } else if (item instanceof KApply) {
          List<K> children = IncompleteCellUtils.flattenCells(item);
          if (children.size() == 1 && children.get(0) == item) {
            final KLabel label = ((KApply) item).klabel();
            Sort s = cfg.getCellSort(label);
            if (s == null) {
              s = cfg.getCellCollectionCell(label);
              if (s == null) {
                throw KEMException.compilerError("Attempting to split non-cell term " + item, item);
              }
            }
            return Collections.singletonMap(s, apply(item));
          }
          // flatten the List<Map<Sort, K>> into a Map<Sort, List<K>>
          Map<Sort, List<K>> multiMap =
              children.stream()
                  .flatMap(e -> getSplit(e).entrySet().stream())
                  .collect(
                      Collectors.groupingBy(
                          Map.Entry::getKey,
                          Collectors.mapping(Map.Entry::getValue, Collectors.toList())));
          return multiMap.entrySet().stream()
              .filter(e -> e.getValue().size() > 0)
              .collect(
                  Collectors.toMap(
                      e -> e.getKey(),
                      e -> {
                        if (e.getValue().size() == 1) {
                          return e.getValue().get(0);
                        } else {
                          return concatenateStarCells(e.getKey(), e.getValue());
                        }
                      }));
        } else if (item instanceof KRewrite rw) {
          Map<Sort, K> splitLeft = new HashMap<>(getSplit(rw.left()));
          Map<Sort, K> splitRight = new HashMap<>(getSplit(rw.right()));
          addDefaultCells(item, splitLeft, splitRight);
          addDefaultCells(item, splitRight, splitLeft);
          assert splitLeft.keySet().equals(splitRight.keySet());
          return splitLeft.keySet().stream()
              .collect(
                  Collectors.toMap(
                      sort -> sort,
                      sort -> KRewrite(splitLeft.get(sort), splitRight.get(sort), rw.att())));
        } else {
          throw KEMException.compilerError(
              "Unexpected kind of term found in cell. Expected variable, "
                  + "apply, or rewrite; found "
                  + item.getClass().getSimpleName(),
              item);
        }
      }

      private K concatenateStarCells(Sort sort, List<K> children) {
        if (cfg.getMultiplicity(sort) != Multiplicity.STAR) {
          throw KEMException.compilerError(
              "Attempting to concatenate cells not of multiplicity=\"*\" "
                  + "into a cell collection.",
              children.iterator().next());
        }
        if (children.size() == 0) {
          return cfg.cfg().getUnit(sort);
        }
        KLabel concat = cfg.cfg().getConcat(sort);
        int ix = children.size();
        K result = children.get(--ix);
        while (ix > 0) {
          result = KApply(concat, children.get(--ix), result);
        }
        return result;
      }

      private void addDefaultCells(K item, Map<Sort, K> splitLeft, Map<Sort, K> splitRight) {
        for (Sort s : Sets.difference(splitLeft.keySet(), splitRight.keySet())) {
          if (cfg.getMultiplicity(s) == Multiplicity.ONE) {
            throw KEMException.compilerError(
                "Cannot rewrite a multiplicity=\"1\" cell to or from the cell unit.", item);
          } else {
            splitRight.put(s, cfg.cfg().getUnit(s));
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

  /**
   * processVars handles a cell fragment variable when it appears solely in a normal term, e.g, rule
   * <k> run => foo(X) ... </k> <x> X:XCellFragment <c> _ </c> </x> but not when it appears with
   * other cells, e.g., rule <k> run => foo(X <c>C</c>) ... </k> <x> X:XCellFragment <c> C </c> </x>
   * resolveIncompleteCellFragment handles such cases, after processVars is done. An idea is to fix
   * invalid cell fragment terms. For example, processVars translates the term `foo(X)` into:
   * foo(<x>-fragment A B </x>-fragment <c>C</c>) then resolveIncompleteCellFragment fixes the term
   * as: foo(<x>-fragment A B <c>C</c> </x>-fragment)
   *
   * <p>Another example: When a cell fragment term consists of only individual cells, processVars
   * does nothing. rule <k> run => foo(B C) ... </k> <x> <a> _ </a> B:BCell C:CCell </x> In this
   * case, resolveIncompleteCellFragment fixes the term `foo(B C)` into: foo(<x>-fragment noACell B
   * C </x>-fragment)
   *
   * <p>Another example: When a cell fragment variable appears only in a normal term, but never in
   * cells, processVars does nothing. rule foo(<b> _ </b> X:XCellFragment) => bar(<b> 2 </b> X) In
   * this case, the cell fragment term in LHS is temporarily decorated by dummy <x> cell label,
   * before processVars, which triggers processVars to split the cell fragment variable. Then
   * resolveIncompleteCellFragment comes in. After resolveIncompleteCellFragment, the dummy cell
   * label is replaced by the corresponding cell fragment label. The pre-/post-processing is done by
   * preprocess/prostprocess.
   *
   * <p>Potential issue: In the above example, if X has no sort casting, it is considered as
   * XCellFragment by default, which may be different with an user's intention.
   *
   * <p>Another potential issue: Currently, one cannot represent a fully filled cell fragment term.
   * e.g., rule <k> foo(X) => .K ... </k> <x> _ => X </x> The above rule replaces the entire cell
   * <x> with the cell fragment term X, but doesn't have a side condition saying that X should be
   * fully decorated. It means that X is given by a partially decorated cell fragment, <x> cell
   * becomes invalid. e.g., foo(<x>-fragment <a> 1 </a> noBCell noCCell </x>-fragment) results in an
   * invalid <x> cell: <x> <a> 1 </a> noBCell noCCell </x> Note that this issue is not specifically
   * about resolveIncompleteCellFragment.
   */
  private K resolveIncompleteCellFragment(K term) {
    return new TransformK() {
      @Override
      public K apply(KApply k0) {
        if (!hasCells(k0)) return super.apply(k0);

        ArrayList<K> klist0 = new ArrayList<K>(Collections.nCopies(k0.klist().size(), null));
        for (int idx = 0; idx < k0.klist().size(); idx++) {
          K item0 = k0.klist().items().get(idx);
          klist0.set(idx, item0);
          if (item0 instanceof KApply k) {

            // incomplete cells remain as #cells(...) after processVars
            if (k.klabel().name().equals("#cells")) {

              Sort cellFragmentSort = nthArgSort(k0.klabel(), idx);
              if (cellFragmentSort == null) {
                throw new IllegalArgumentException(
                    "Not found " + idx + "th argument sort of " + k0.klabel());
              }

              // a cell fragment term
              if (cellFragmentSort.name().endsWith("Fragment")) {

                Sort cellSort =
                    Sort(
                        cellFragmentSort
                            .name()
                            .substring(0, cellFragmentSort.name().indexOf("Fragment")));
                KLabel cellLabel = cfg.cfg().getCellLabel(cellSort);

                List<Sort> subcellSorts = cfg.getChildren(cellLabel);

                /*
                  fix an invalid cell fragment term, e.g.,

                  Case 1.
                  from
                    foo(<x>-fragment A B </x>-fragment <c>C</c>)
                  into
                    foo(<x>-fragment A B <c>C</c> </x>-fragment)

                  Case 2.
                  from
                    foo(B C)
                  into
                    foo(<x>-fragment noACell B C </x>-fragment)
                */

                // fill individual cells first, starting with empty
                KApply cellFragment = null;
                ArrayList<K> klist =
                    new ArrayList<K>(Collections.nCopies(subcellSorts.size(), null));
                for (K item :
                    IncompleteCellUtils.flattenCells(k)) { // #cells(#cells(x,y),z) => [x,y,z]
                  if (item instanceof KApply kapp) {
                    if (cfg.cfg().isCellLabel(kapp.klabel())) {
                      Sort sort = cfg.getCellSort(kapp.klabel());
                      if (!subcellSorts.contains(sort)) {
                        throw new IllegalArgumentException(
                            "No such sub-cell " + sort + " in the cell " + cellLabel);
                      }
                      klist.set(subcellSorts.indexOf(sort), item);
                    } else if (kapp.klabel().name().endsWith("-fragment")) {
                      cellFragment = kapp;
                      assert cellFragment.klist().size() == subcellSorts.size();
                      assert cellFragment.klabel().name().equals(cellLabel.name() + "-fragment");
                    } else {
                      throw KEMException.compilerError("Unsupported cell fragment element.", item);
                    }
                  } else if (item instanceof KVariable var) {
                    VarInfo varinfo = null;
                    if (variables.containsKey(var)) {
                      varinfo = variables.get(var);
                    }
                    if (!var.att().contains(Att.SORT(), Sort.class) && varinfo != null) {
                      if (varinfo.var != null) var = varinfo.var;
                    }
                    if (var.att().contains(Att.SORT(), Sort.class)) {
                      Sort sort = var.att().get(Att.SORT(), Sort.class);
                      if (cfg.cfg().isCell(sort)) {
                        if (!subcellSorts.contains(sort)) {
                          throw new IllegalArgumentException(
                              "No such sub-cell " + sort + " in the cell " + cellLabel);
                        }
                        klist.set(subcellSorts.indexOf(sort), item);
                      } else {
                        // if the variable is not explicitly sort-casted, then its sort information
                        // should be found in other places
                        if (varinfo != null
                            && varinfo.remainingCells != null
                            && varinfo.remainingCells.size() == 1) {
                          Sort s = Iterables.getOnlyElement(varinfo.remainingCells);
                          if (cfg.cfg().isCell(s)) {
                            if (!subcellSorts.contains(s)) {
                              throw new IllegalArgumentException(
                                  "No such sub-cell " + s + " in the cell " + cellLabel);
                            }
                            klist.set(subcellSorts.indexOf(s), item);
                            continue;
                          }
                        }
                        throw KEMException.compilerError(
                            "Unsupported cell fragment element. Not found sort info.", item);
                      }
                    } else {
                      throw KEMException.compilerError(
                          "Unsupported cell fragment element. Not found sort info.", item);
                    }
                  } else {
                    // TODO: support when item instanceof KRewrite
                    throw KEMException.compilerError("Unsupported cell fragment element.", item);
                  }
                }

                // fill remaining cells, considering a split cell fragment variable if any
                for (int i = 0; i < subcellSorts.size(); i++) {
                  if (klist.get(i) == null) {
                    if (cellFragment != null) {
                      klist.set(i, cellFragment.klist().items().get(i));
                    } else {
                      if (cfg.getMultiplicity(subcellSorts.get(i)) == Multiplicity.ONE) {
                        klist.set(i, cfg.getCellAbsentTerm(subcellSorts.get(i)));
                      } else { // Multiplicity.OPTIONAL || Multiplicity.STAR
                        klist.set(i, cfg.cfg().getUnit(subcellSorts.get(i)));
                      }
                    }
                  }
                }

                klist0.set(idx, KApply(KLabel(cellLabel.name() + "-fragment"), KList(klist)));
              }
            }
          }
        }
        return KApply(k0.klabel(), KList(klist0), k0.att());
      }
    }.apply(term);
  }

  /** Pre-process terms before processVar */
  public synchronized Sentence preprocess(Sentence s) {
    if (s instanceof RuleOrClaim) {
      return preprocess((RuleOrClaim) s);
    } else {
      return s;
    }
  }

  /** Post-process terms after processVar */
  public synchronized Sentence postprocess(Sentence s) {
    if (s instanceof RuleOrClaim) {
      return postprocess((RuleOrClaim) s);
    } else {
      return s;
    }
  }

  private RuleOrClaim preprocess(RuleOrClaim rule) {
    return rule.newInstance(
        preprocess(rule.body()),
        preprocess(rule.requires()),
        preprocess(rule.ensures()),
        rule.att());
  }

  private RuleOrClaim postprocess(RuleOrClaim rule) {
    return rule.newInstance(
        postprocess(rule.body()),
        postprocess(rule.requires()),
        postprocess(rule.ensures()),
        rule.att());
  }

  /**
   * When a cell fragment variable appears only in <k> cell, e.g., rule foo(<b> _ </b>
   * X:XCellFragment) => bar(<b> 2 </b> X) preprocess temporarily arguments the cell fragment term
   * in LHS using its parent cell label, e.g., rule foo(<x> <b> _ </b> X:XCellFragment </x>) =>
   * bar(<b> 2 </b> X) Now, the cell fragment variable X will be split by processVars.
   */
  private K preprocess(K term) {
    // find all of cell fragment variables
    HashMap<KVariable, HashSet<K>> cellFragmentVars = new HashMap<>();
    new VisitK() {
      @Override
      public void apply(KApply k) {
        if (k.klabel().name().equals("#cells")) {
          for (int i = 0; i < k.klist().size(); i++) {
            K item = k.klist().items().get(i);
            if (item instanceof KVariable var) {
              if (var.att().contains(Att.SORT(), Sort.class)) {
                Sort sort = var.att().get(Att.SORT(), Sort.class);
                if (!cfg.cfg().isCell(sort)) {
                  if (!cellFragmentVars.containsKey(var)) {
                    cellFragmentVars.put(var, new HashSet<>());
                  }
                  cellFragmentVars.get(var).add(k);
                }
              } else {
                if (!cellFragmentVars.containsKey(var)) {
                  cellFragmentVars.put(var, new HashSet<>());
                }
                cellFragmentVars.get(var).add(k);
              }
            }
          }
        } else {
          super.apply(k);
        }
      }
    }.apply(term);

    if (cellFragmentVars.isEmpty()) {
      return term;
    }

    // drop cell fragment variables that appear outside <k> cell, in non-function rules
    if (!labelInfo.isFunction(term)) {
      new VisitK() {
        private boolean inKCell = false;

        @Override
        public void apply(KApply k) {
          if (k.klabel().name().equals("<k>")) {
            assert !inKCell;
            inKCell = true;
            super.apply(k);
            inKCell = false;
          } else {
            super.apply(k);
          }
        }

        @Override
        public void apply(KVariable var) {
          if (!inKCell) {
            cellFragmentVars.remove(var);
          }
        }
      }.apply(term);
    }

    if (cellFragmentVars.isEmpty()) {
      return term;
    }

    HashSet<K> cellFragmentVarsCell = new HashSet<>();
    for (HashSet<K> cells : cellFragmentVars.values()) {
      cellFragmentVarsCell.addAll(cells);
    }

    // decorate such cell fragment terms with their parent cell label
    return new TransformK() {
      @Override
      public K apply(KApply k0) {
        if (hasCells(k0)) {
          ArrayList<K> klist0 = new ArrayList<K>(Collections.nCopies(k0.klist().size(), null));
          for (int idx = 0; idx < k0.klist().size(); idx++) {
            K item0 = k0.klist().items().get(idx);
            klist0.set(idx, item0);
            if (item0 instanceof KApply k) {
              if (k.klabel().name().equals("#cells")) {
                if (cellFragmentVarsCell.contains(k)) {
                  Sort cellFragmentSort = nthArgSort(k0.klabel(), idx);
                  if (cellFragmentSort == null) {
                    throw new IllegalArgumentException(
                        "Not found " + idx + "th argument sort of " + k0.klabel());
                  }
                  if (cellFragmentSort.name().endsWith("Fragment")) {
                    Sort cellSort =
                        Sort(
                            cellFragmentSort
                                .name()
                                .substring(0, cellFragmentSort.name().indexOf("Fragment")));
                    KLabel cellLabel = cfg.cfg().getCellLabel(cellSort);
                    klist0.set(
                        idx, KApply(cellLabel, KList(item0), Att.empty().add(Att.DUMMY_CELL())));
                  }
                }
              }
            }
          }
          return KApply(k0.klabel(), KList(klist0), k0.att());
        }
        return super.apply(k0);
      }

      @Override
      public K apply(KRewrite k) {
        K left = super.apply(k.left());
        return KRewrite(left, k.right(), k.att());
      }
    }.apply(term);
  }

  // remove the dummy cell decoration introduced by preprocess
  private K postprocess(K term) {
    return new TransformK() {
      @Override
      public K apply(KApply k) {
        if (k.att().contains(Att.DUMMY_CELL())) {
          KLabel klabel = KLabel(k.klabel().name() + "-fragment");
          return KApply(klabel, k.klist(), k.att());
        }
        return super.apply(k);
      }
    }.apply(term);
  }

  private boolean hasCells(KApply k) {
    for (int i = 0; i < k.klist().size(); i++) {
      K item = k.klist().items().get(i);
      if (item instanceof KApply && ((KApply) item).klabel().name().equals("#cells")) {
        return true;
      }
    }
    return false;
  }

  // find nth argument sort for a given klabel
  // if multiple signiture exist, then return arbitrary one of them that is not K
  private Sort nthArgSort(KLabel klabel, int n) {
    java.util.Set<Tuple2<scala.collection.immutable.Seq<Sort>, Sort>> sigs =
        mutable(JavaConversions.mapAsJavaMap(module.signatureFor()).get(klabel));
    if (sigs == null) {
      throw new IllegalArgumentException("Not found signature for label: " + klabel);
    }
    Sort sort = null;
    for (Tuple2<scala.collection.immutable.Seq<Sort>, Sort> sig : sigs) {
      List<Sort> sorts = JavaConversions.seqAsJavaList(sig._1());
      if (n >= sorts.size()) continue;
      sort = sorts.get(n);
      if (!sort.equals(Sorts.K())) {
        return sort;
      }
    }
    return sort;
  }
}
