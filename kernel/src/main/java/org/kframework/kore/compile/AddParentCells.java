// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore.compile;

import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.kore.KORE.*;

/**
 * Add omitted parent cells to a term written using configuration abstraction.
 * It only completes the contents of existing cells, so an earlier pass should add
 * a top cell around rule bodies if completion to the top is desired.
 * Newly inserted cells have dots if and only if the parent cell they were added under did
 * (dots are elimiinated in the {@link CloseCells} pass).
 */
public class AddParentCells {

    private final ConcretizationInfo cfg;

    public AddParentCells(ConfigurationInfo configInfo, LabelInfo labelInfo) {
        cfg = new ConcretizationInfo(configInfo, labelInfo);
    }

    Stream<K> streamSideCells(K side) {
        List<K> cells = IncompleteCellUtils.flattenCells(side);
        // TODO error handling
        return cells.stream();
    }

    protected List<KApply> makeParents(KLabel parent, boolean ellipses,
                                       List<K> allChildren) {
        // List<KRewrite> rewrites
//        rewrites.stream().map(r -> r.left()).flatMap(t -> if(t.));

        List<K> children = allChildren.stream().filter(t -> !(t instanceof KRewrite)).collect(Collectors.toList());
        List<KRewrite> rewrites = allChildren.stream().filter(t -> t instanceof KRewrite).map(t -> (KRewrite) t).collect(Collectors.toList());

        // see if all children can fit together
        Set<Sort> usedCells = Sets.newHashSet();
        BiFunction<List<K>, Set<Sort>, Boolean> useCells = (cells, used) -> {
            for (K k : cells) {
                Sort sort = cfg.getCellSort(k);
                if (cfg.getMultiplicity(sort) != ConfigurationInfo.Multiplicity.STAR) {
                    if (used.contains(sort)) {
                        return false;
                    } else {
                        used.add(sort);
                    }
                }
            }
            return true;
        };

        boolean allFitTogether = useCells.apply(children, usedCells);
        if (allFitTogether) {
            Function<Function<KRewrite, K>, List<K>> flattenRewrite = f -> rewrites.stream().map(f).flatMap
                    (this::streamSideCells).collect(Collectors.toList());

            List<K> leftChildren = flattenRewrite.apply(KRewrite::left);
            Set<Sort> usedLeft = Sets.newHashSet(usedCells);
            boolean leftFit = useCells.apply(leftChildren, usedLeft);
            List<K> rightChildren = flattenRewrite.apply(KRewrite::right);
            Set<Sort> usedRight = Sets.newHashSet(usedCells);
            boolean rightFit = useCells.apply(rightChildren, usedRight);
            allFitTogether = leftFit && rightFit;
        }
        if (allFitTogether) {
            return Lists.newArrayList(IncompleteCellUtils.make(parent, ellipses, allChildren, ellipses));
        }

        // Otherwise, see if they are forced to have separate parents...

        boolean forcedSeparate = true;
        if (!children.isEmpty()) {
            Sort label = cfg.getCellSort(children.get(0));
            if (cfg.getMultiplicity(label) == ConfigurationInfo.Multiplicity.STAR) {
                forcedSeparate = false;
            } else {
                for (K child : children) {
                    Sort sort = cfg.getCellSort(child);
                    if (!sort.equals(label)) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
            if (forcedSeparate) {
                for (KRewrite rew : rewrites) {
                    if (!(streamSideCells(rew.left()).anyMatch(l -> cfg.getCellSort(l).equals(label))
                            || streamSideCells(rew.left()).anyMatch(l -> cfg.getCellSort(l).equals(label)))) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
        }
        if (forcedSeparate) {
            for (KRewrite rew1 : rewrites) {
                for (KRewrite rew2 : rewrites) {
                    Set<Sort> left1NonRepeatable = streamSideCells(rew1.left()).map(cfg::getCellSort)
                            .filter(l -> cfg.getMultiplicity(l) != ConfigurationInfo.Multiplicity.STAR)
                            .collect(Collectors.toSet());
                    boolean lhsConflict = streamSideCells(rew2.left()).map(cfg::getCellSort)
                            .filter(left1NonRepeatable::contains).count() >= 1;

                    Set<Sort> right1NonRepeatable = streamSideCells(rew1.right()).map(cfg::getCellSort)
                            .filter(l -> cfg.getMultiplicity(l) != ConfigurationInfo.Multiplicity.STAR)
                            .collect(Collectors.toSet());
                    boolean rhsConflict = streamSideCells(rew2.right()).map(cfg::getCellSort)
                            .filter(right1NonRepeatable::contains).count() >= 1;
                    if (!(lhsConflict || rhsConflict)) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
        }
        if (forcedSeparate) {
            return allChildren.stream()
                    .map(k -> IncompleteCellUtils.make(parent, ellipses, k, ellipses))
                    .collect(Collectors.toList());
        }

        // They were also not forced to be separate
        throw KEMException.criticalError("Ambiguous completion");
    }

    boolean isCompletionItem(K k) {
        return (k instanceof KApply || k instanceof KRewrite || k instanceof KVariable)
                && getLevel(k).isPresent();
    }

    Optional<Integer> getLevel(KApply k) {
        int level = cfg.getLevel(k.klabel());
        if (level >= 0) {
            return Optional.of(level);
        } else {
            return Optional.empty();
        }
    }

    Optional<Integer> getLevel(K k) {
        if (k instanceof KApply) {
            return getLevel((KApply) k);
        } else if (k instanceof KVariable) {
            if (k.att().contains(Attribute.SORT_KEY)) {
                Sort sort = Sort(k.att().<String>get(Attribute.SORT_KEY).get());
                int level = cfg.cfg.getLevel(sort);
                if (level >= 0) {
                    return Optional.of(level);
                }
            }
            return Optional.empty();
        } else {
            KRewrite rew = (KRewrite) k;
            List<K> cells = IncompleteCellUtils.flattenCells(rew.left());
            cells.addAll(IncompleteCellUtils.flattenCells(rew.right()));
            Optional<Integer> level = Optional.empty();
            for (K item : cells) {
                Optional<Integer> level2 = getLevel(item);
                if (item instanceof KVariable && !level2.isPresent()) {
                    continue;
                }
                if (!level.isPresent()) {
                    level = level2;
                } else if (!level.equals(level2)) {
                    throw KEMException.criticalError("Can't mix cells at different levels under a rewrite");
                }
                // else level is already correct
            }
            return level;
        }
    }

    Optional<KLabel> getParent(K k) {
        if (k instanceof KApply) {
            if (((KApply) k).klabel().equals(KLabel("#cells"))) {
                List<K> items = ((KApply) k).klist().items();
                if (items.isEmpty()) {
                    return Optional.empty();
                }
                Optional<KLabel> parent = getParent(items.get(0));
                for (K item : items) {
                    if (!parent.equals(getParent(item))) {
                        throw KEMException.criticalError("Can't mix cells with different parents levels under a rewrite");
                    }
                }
                return parent;
            } else {
                return Optional.of(cfg.getParent(((KApply) k).klabel()));
            }
        } else if (k instanceof KVariable) {
            Sort sort = Sort(k.att().<String>get(Attribute.SORT_KEY).get());
            return Optional.of(cfg.getParent(sort));
        } else {
            Optional<KLabel> leftParent = getParent(((KRewrite) k).left());
            Optional<KLabel> rightParent = getParent(((KRewrite) k).right());
            if (!leftParent.isPresent()) {
                return rightParent;
            }
            if (!rightParent.isPresent()) {
                return leftParent;
            }
            if (leftParent.equals(rightParent)) {
                return leftParent;
            } else {
                throw KEMException.criticalError("All cells on the left and right of a rewrite must have the same parent: " + k);
            }
        }
    }

    K concretizeCell(K k) {
        if (!(k instanceof KApply)) {
            return k;
        } else {
            KApply app = (KApply) k;
            KLabel target = app.klabel();
            if (cfg.isLeafCell(target)) {
                return k;
            }
            List<K> children = Lists.newArrayList();
            List<K> otherChildren = Lists.newArrayList();
            int ix = 0;
            boolean ellipses = IncompleteCellUtils.isOpenLeft(app)
                    || IncompleteCellUtils.isOpenRight(app);
            for (K item : IncompleteCellUtils.getChildren(app)) {
                if (isCompletionItem(item)) {
                    children.add(item);
                } else {
                    otherChildren.add(item);
                }
                ++ix;
            }
            if (children.isEmpty()) {
                return k;
            }

            int targetLevel = cfg.getLevel(target) + 1;
            TreeMap<Integer, Collection<K>> levelMap = new TreeMap<>();
            Multimap<Integer, K> levels = Multimaps.newMultimap(levelMap, ArrayList::new);
            for (K child : children) {
                levels.put(getLevel(child).get(), child);
            }
            while (levelMap.lastKey() > targetLevel) {
                Collection<K> level = levels.removeAll(levelMap.lastKey());
                for (Map.Entry<KLabel, List<K>> e : level.stream().collect(Collectors.groupingBy(t -> getParent(t).get())).entrySet()) {
                    KLabel parent = e.getKey();
                    List<KApply> newCells = makeParents(parent, ellipses, e.getValue());
                    levels.putAll(cfg.getLevel(parent), newCells);
                }
            }
            otherChildren.addAll(levels.removeAll(levelMap.lastKey()));
            return IncompleteCellUtils.make(target, ellipses, otherChildren, ellipses);
        }
    }

    K concretize(K term) {
        if (term instanceof KApply) {
            KApply app = (KApply) term;
            KApply newTerm = KApply(app.klabel(), KList(app.klist().stream()
                    .map(this::concretize).collect(Collectors.toList())));
            if (cfg.isParentCell(newTerm.klabel())) {
                return concretizeCell(newTerm);
            } else {
                return newTerm;
            }
        } else if (term instanceof KRewrite) {
            KRewrite rew = (KRewrite) term;
            return KRewrite(concretize(rew.left()), concretize(rew.right()));
        } else if (term instanceof KSequence) {
            return KSequence(((KSequence) term).stream()
                    .map(this::concretize).collect(Collectors.toList()));
        } else {
            return term;
        }
    }

    public Sentence concretize(Sentence m) {
        if (m instanceof Rule) {
            Rule r = (Rule) m;
            return new Rule(concretize(r.body()), r.requires(), r.ensures(), r.att());
        } else if (m instanceof Context) {
            Context c = (Context) m;
            return new Context(concretize(c.body()), c.requires(), c.att());
        } else {
            return m;
        }
    }
}
