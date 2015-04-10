// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore.compile;

import com.google.common.collect.Lists;

import java.util.*;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.collect.Sets;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.*;
import org.kframework.kore.*;

import static org.kframework.kore.KORE.*;

/**
 * Add omitted parent cells to a term written using configuration abstraction.
 * It only completes the contents of existing cells, so an earlier pass should add
 * a top cell around rule bodies if completion to the top is desired.
 * Newly inserted cells have dots if and only if the parent cell they were added under did
 * (dots are elimiinated in the {@link CloseCells} pass).
 */
public class ConcretizeConfiguration {

    private final ConcretizationInfo cfg;

    public ConcretizeConfiguration(ConfigurationInfo configInfo, LabelInfo labelInfo) {
        cfg = new ConcretizationInfo(configInfo, labelInfo);
    }

    Stream<KApply> streamSideCells(K side) {
        List<K> cells = IncompleteCellUtils.flattenCells(side);
        // TODO error handling
        return (Stream<KApply>) (Object) cells.stream();
    }

    protected final static KApply dots = KApply(KLabel("#dots"));

    KApply makeCell(KLabel label, boolean ellipses, K item) {
        return IncompleteCellUtils.make(label, ellipses, item, ellipses);
    }

    KApply makeCell(KLabel label, boolean ellipses, List<? extends K> children) {
        return IncompleteCellUtils.make(label, ellipses, children, ellipses);
    }

    protected List<KApply> makeParents(KLabel parent, boolean ellipses,
                                       List<? extends K> allChildren) {
        // List<KRewrite> rewrites
//        rewrites.stream().map(r -> r.left()).flatMap(t -> if(t.));

        List<KApply> children = allChildren.stream().filter(t -> t instanceof KApply).map(t -> (KApply) t).collect(Collectors.toList());
        List<KRewrite> rewrites = allChildren.stream().filter(t -> t instanceof KRewrite).map(t -> (KRewrite) t).collect(Collectors.toList());

        // see if all children can fit together
        Set<KLabel> usedCells = Sets.newHashSet();
        BiFunction<List<KApply>, Set<KLabel>, Boolean> useCells = (cells, used) -> {
            for (KApply k : cells) {
                KLabel label = k.klabel();
                if (cfg.getMultiplicity(label) != ConfigurationInfo.Multiplicity.STAR) {
                    if (used.contains(label)) {
                        return false;
                    } else {
                        used.add(label);
                    }
                }
            }
            return true;
        };

        boolean allFitTogether = useCells.apply(children, usedCells);
        if (allFitTogether) {
            Function<Function<KRewrite, K>, List<KApply>> flattenRewrite = f -> rewrites.stream().map(f).flatMap
                    (this::streamSideCells).collect(Collectors.toList());

            List<KApply> leftChildren = flattenRewrite.apply(KRewrite::left);
            Set<KLabel> usedLeft = Sets.newHashSet(usedCells);
            boolean leftFit = useCells.apply(leftChildren, usedLeft);
            List<KApply> rightChildren = flattenRewrite.apply(KRewrite::right);
            Set<KLabel> usedRight = Sets.newHashSet(usedCells);
            boolean rightFit = useCells.apply(rightChildren, usedRight);
            allFitTogether = leftFit && rightFit;
        }
        if (allFitTogether) {
            return Lists.newArrayList(makeCell(parent, ellipses, allChildren));
        }

        // Otherwise, see if they are forced to have separate parents...

        boolean forcedSeparate = true;
        if (!children.isEmpty()) {
            KLabel label = children.get(0).klabel();
            if (cfg.getMultiplicity(label) == ConfigurationInfo.Multiplicity.STAR) {
                forcedSeparate = false;
            } else {
                for (KApply child : children) {
                    if (!child.klabel().equals(label)) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
            if (forcedSeparate) {
                for (KRewrite rew : rewrites) {
                    if (!(streamSideCells(rew.left()).anyMatch(l -> l.klabel().equals(label))
                            || streamSideCells(rew.left()).anyMatch(l -> l.klabel().equals(label)))) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
        }
        if (forcedSeparate) {
            for (KRewrite rew1 : rewrites) {
                for (KRewrite rew2 : rewrites) {
                    Set<KLabel> left1NonRepeatable = streamSideCells(rew1.left()).map(KApply::klabel)
                            .filter(l -> cfg.getMultiplicity(l) != ConfigurationInfo.Multiplicity.STAR)
                            .collect(Collectors.toSet());
                    boolean lhsConflict = streamSideCells(rew2.left()).map(KApply::klabel)
                            .filter(left1NonRepeatable::contains).count() >= 1;

                    Set<KLabel> right1NonRepeatable = streamSideCells(rew1.right()).map(KApply::klabel)
                            .filter(l -> cfg.getMultiplicity(l) != ConfigurationInfo.Multiplicity.STAR)
                            .collect(Collectors.toSet());
                    boolean rhsConflict = streamSideCells(rew2.right()).map(KApply::klabel)
                            .filter(right1NonRepeatable::contains).count() >= 1;
                    if (!(lhsConflict || rhsConflict)) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
        }
        if (forcedSeparate) {
            return allChildren.stream().map(k -> makeCell(parent, ellipses, k)).collect(Collectors.toList());
        }

        // They were also not forced to be separate
        throw new IllegalArgumentException("Ambiguous completion");
    }

    boolean isCompletionItem(K k) {
        return (k instanceof KApply || k instanceof KRewrite)
                && !(k instanceof KVariable) && getLevel(k).isPresent();
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
        } else {
            KRewrite rew = (KRewrite) k;
            List<K> cells = IncompleteCellUtils.flattenCells(rew.left());
            cells.addAll(IncompleteCellUtils.flattenCells(rew.right()));
            Optional<Integer> level = Optional.empty();
            for (K item : cells) {
                if (item instanceof KVariable) {
                    continue;
                }
                Optional<Integer> level2 = getLevel(item);
                if (!level.isPresent()) {
                    level = level2;
                } else if (!level.equals(level2)) {
                    throw new AssertionError("Can't mix cells at different levels under a rewrite");
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
                        throw new AssertionError("Can't mix cells with different parents levels under a rewrite");
                    }
                }
                return parent;
            } else {
                return Optional.of(cfg.getParent(((KApply) k).klabel()));
            }
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
                throw new AssertionError("All cells on the left and right of a rewrite must have the same parent: " + k);
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
            boolean ellipses = IncompleteCellUtils.isOpenLeft(app)
                    || IncompleteCellUtils.isOpenRight(app);
            int ix = 0;
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
            return makeCell(target, ellipses, otherChildren);
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
            return new Context(c.body(), c.requires(), c.att());
        } else {
            return m;
        }
    }

    ModuleTransformer moduleTransormer = ModuleTransformer.from(this::concretize);

    public Module concretize(Module m) {
        return moduleTransormer.apply(m);
    }

    public Definition concretize(Definition d) {
        return DefinitionTransformer.from(this::concretize).apply(d);
    }
}
