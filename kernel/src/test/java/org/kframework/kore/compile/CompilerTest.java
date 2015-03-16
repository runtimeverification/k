package org.kframework.kore.compile;


import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;
import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;
import org.kframework.kore.*;

import java.io.FileFilter;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.kore.KORE.*;

public class CompilerTest {

    static class Configuration {

        Map<KLabel, Integer> levels = new HashMap();
        Map<KLabel, KLabel> parents = new HashMap();
        Multimap<KLabel, KLabel> children = HashMultimap.create();

        public enum Multiplicity {ONE, OPTIONAL, STAR}

        ;
        Map<KLabel, Multiplicity> multiplicities = new HashMap();

        private void addCell(String parent, String child, int level, Multiplicity m) {
            if (parent != null) {
                parents.put(KLabel(child), KLabel(parent));
                children.put(KLabel(parent), KLabel(child));
            }
            levels.put(KLabel(child), level);
            multiplicities.put(KLabel(child), m);
        }

        Configuration() {
            addCell(null, "<T>", 0, Multiplicity.ONE);
            addCell("<T>", "<ts>", 1, Multiplicity.ONE);
            addCell("<T>", "<state>", 1, Multiplicity.ONE);
            addCell("<ts>", "<t>", 2, Multiplicity.STAR);
            addCell("<ts>", "<scheduler>", 2, Multiplicity.ONE);
            addCell("<t>", "<k>", 3, Multiplicity.ONE);
            addCell("<t>", "<env>", 3, Multiplicity.ONE);
            addCell("<t>", "<msg>", 3, Multiplicity.STAR);
        }

        Comparator<KLabel> comparator() {
            return Comparator.comparing(levels::get);
        }

        int getLevel(KLabel k) {
            return levels.get(k);
        }

        KLabel getParent(KLabel k) {
            return parents.get(k);
        }

        Multiplicity getMultiplicity(KLabel k) {
            return multiplicities.get(k);
        }

        boolean isLeafCell(KLabel k) {
            return !parents.values().contains(k);
        }
    }

    final Configuration cfg = new Configuration();

    Stream<KApply> streamSideCells(K side) {
        if (side instanceof KApply && ((KApply) side).klabel().equals(KLabel("#cells")))
            return (Stream<KApply>) (Object) ((KApply) side).klist().stream();
        else
            return Stream.of((KApply) side);
    }

    List<KApply> makeParents(KLabel parent, List<? extends K> allChildren) {
        // List<KRewrite> rewrites
//        rewrites.stream().map(r -> r.left()).flatMap(t -> if(t.));

        List<KApply> children = allChildren.stream().filter(t -> t instanceof KApply).map(t -> (KApply) t).collect(Collectors.toList());
        List<KRewrite> rewrites = allChildren.stream().filter(t -> t instanceof KRewrite).map(t -> (KRewrite) t).collect(Collectors.toList());
        // see if all children can fit together
        boolean allFitTogether = true;

        Set<KLabel> usedCells = Sets.newHashSet();
        BiFunction<List<KApply>, Set<KLabel>, Boolean> useCells = (cells, used) -> {
            for (KApply k : cells) {
                KLabel label = k.klabel();
                if (cfg.getMultiplicity(label) != Configuration.Multiplicity.STAR) {
                    if (used.contains(label)) {
                        return false;
                    } else {
                        used.add(label);
                    }
                }
            }
            return true;
        };

        allFitTogether = useCells.apply(children, usedCells);
        if (allFitTogether) {
            Function<Function<KRewrite, K>, List<KApply>> flattenRewrite = f -> rewrites.stream().map(f).flatMap
                    (t -> streamSideCells(t)).collect(Collectors.toList());

            List<KApply> leftChildren = flattenRewrite.apply(t -> t.left());
            Set<KLabel> usedLeft = Sets.newHashSet(usedCells);
            boolean leftFit = useCells.apply(leftChildren, usedLeft);
            List<KApply> rightChildren = flattenRewrite.apply(t -> t.right());
            Set<KLabel> usedRight = Sets.newHashSet(usedCells);
            boolean rightFit = useCells.apply(rightChildren, usedRight);
            allFitTogether = leftFit && rightFit;
        }
        if (allFitTogether) {
            return Lists.newArrayList(KApply(parent, KList(allChildren)));
        }

        // Otherwise, see if they are forced to have separate parents...

        boolean forcedSeparate = true;
        if (!children.isEmpty()) {
            KLabel label = children.get(0).klabel();
            if (cfg.getMultiplicity(label) == Configuration.Multiplicity.STAR) {
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
                    Set<KLabel> left1NonRepeatable = streamSideCells(rew1.left()).map(t -> t.klabel())
                            .filter(l -> cfg.getMultiplicity(l) != Configuration.Multiplicity.STAR)
                            .collect(Collectors.toSet());
                    boolean lhsConflict = streamSideCells(rew2.left()).map(t -> t.klabel())
                            .filter(l -> left1NonRepeatable.contains(l)).count() >= 1;

                    Set<KLabel> right1NonRepeatable = streamSideCells(rew1.right()).map(t -> t.klabel())
                            .filter(l -> cfg.getMultiplicity(l) != Configuration.Multiplicity.STAR)
                            .collect(Collectors.toSet());
                    boolean rhsConflict = streamSideCells(rew2.right()).map(t -> t.klabel())
                            .filter(l -> right1NonRepeatable.contains(l)).count() >= 1;
                    if (!(lhsConflict || rhsConflict)) {
                        forcedSeparate = false;
                        break;
                    }
                }
            }
        }
        if (forcedSeparate) {
            return allChildren.stream().map(k -> KApply(parent, k)).collect(Collectors.toList());
        }

        // They were also not forced to be separate
        throw new IllegalArgumentException("Ambiguous completion");
    }

    boolean isCompletionItem(K k) {
        return (k instanceof KApply || k instanceof KRewrite)
                && getLevel(k).isPresent();
    }

    Optional<Integer> getLevel(K k) {
        if (k instanceof KApply) {
            if (((KApply) k).klabel().equals(KLabel("#cells"))) {
                List<K> items = ((KApply) k).klist().items();
                if (items.isEmpty()) {
                    return Optional.empty();
                }
                Optional<Integer> level = getLevel(items.get(0));
                for (K item : items) {
                    if (!getLevel(item).equals(level)) {
                        throw new AssertionError("Can't mix cells at different levels under a rewrite");
                    }
                }
                return level;
            } else {
                return Optional.of(cfg.getLevel(((KApply) k).klabel()));
            }
        } else {
            Optional<Integer> leftLevel = getLevel(((KRewrite) k).left());
            Optional<Integer> rightLevel = getLevel(((KRewrite) k).right());
            if (!leftLevel.isPresent()) {
                return rightLevel;
            }
            if (!rightLevel.isPresent()) {
                return leftLevel;
            }
            if (leftLevel.equals(rightLevel))
                return leftLevel;
            else
                throw new AssertionError("The left and right of a rewrite must have the same level: " + k);
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

    Optional<KLabel> getParent2(K k) {
        return Optional.of(null);
    }

    K concretize(K k) {
        if (!(k instanceof KApply)) {
            return k;
        } else {
            KApply app = (KApply) k;
            KLabel target = app.klabel();
            if (cfg.isLeafCell(target)) {
                return k;
            }
            List<K> children = app.klist().stream().filter(this::isCompletionItem).collect(Collectors.toList());
            List<K> otherChildren = app.klist().stream().filter(kk -> !isCompletionItem(kk)).collect(Collectors.toList());

            int targetLevel = cfg.getLevel(target) + 1;
            TreeMap<Integer, List<K>> levels =
                    new TreeMap(children.stream().collect(Collectors.groupingBy(t -> getLevel(t).get())));
            while (levels.lastKey() > targetLevel) {
                List<K> level = levels.remove(levels.lastKey());
                for (Map.Entry<KLabel, List<K>> e : level.stream().collect(Collectors.groupingBy(t -> getParent(t).get())).entrySet()) {
                    KLabel parent = e.getKey();
                    List<KApply> newCells = makeParents(parent, e.getValue());
                    levels.compute(cfg.getLevel(parent),
                            (kk, v) -> {
                                if (v == null) {
                                    return (List<K>) (Object) newCells;
                                } else {
                                    v.addAll(newCells);
                                    return v;
                                }
                            });
                }
            }
            List<K> wrappedChildren = levels.remove(levels.lastKey());
            otherChildren.addAll(wrappedChildren);
            return KApply(target, KList(otherChildren));
        }
    }

    @Test
    public void testOneLeafCellNoCompletion() {
        K term = cell("<k>", intToToken(2));
        K expected = cell("<k>", intToToken(2));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testTwoCellsNoCompletion() {
        K term = cell("<t>", cell("<k>", intToToken(2)));
        K expected = cell("<t>", cell("<k>", intToToken(2)));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testTwoCellsCompletion() {
        K term = cell("<ts>", cell("<k>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(2))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testMultiplicitySeparate() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", cell("<k>", intToToken(2))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testMultiplicityShared() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<env>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(1)), cell("<env>", intToToken(2))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test(expected = IllegalArgumentException.class)
    public void testAmbiguityError() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)), cell("<env>", intToToken(2)));
        concretize(term);
    }

    @Test
    public void testDeep2() {
        Assert.assertEquals(Lists.newArrayList(cell("<ts>", cell("<t>", intToToken(1)), cell("<t>", intToToken(2)))),
                makeParents(KLabel("<ts>"), Lists.newArrayList(cell("<t>", intToToken(1)), cell("<t>", intToToken(2)))));
    }

    @Test
    public void testDeep() {
        K term = cell("<T>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<T>", cell("<ts>", cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", cell("<k>", intToToken(2)))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    @Ignore
    public void testCells() {
        // TODO
    }

    @Test
    public void testRewrites() {
        K term = cell("<T>", cell("<k>", intToToken(1)), KRewrite(cell("<k>", intToToken(2)), cell("<k>")));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", KRewrite(cell("<k>", intToToken(2)), cell("<k>")))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testRewriteWithCells() {
        K term = cell("<T>", cell("<k>", intToToken(1)), KRewrite(cells(cell("<k>", intToToken(2)), cell("<msg>")), cell("<k>")));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", KRewrite(cells(cell("<k>", intToToken(2)), cell("<msg>")), cell("<k>")))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testEmptySide() {
        K term = cell("<T>", cell("<k>"), KRewrite(cell("<msg>"), cells()));
        K expected = cell("<T>", cell("<ts>", cell("<t>", cell("<k>"), KRewrite(cell("<msg>"), cells()))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testTwoRewritesFit() {
        K term = cell("<T>", KRewrite(cells(), cell("<k>", intToToken(1))),
                KRewrite(cell("<k>", intToToken(2)), cells()));
        K expected = cell("<T>", cell("<ts>", cell("<t>",
                KRewrite(cells(), cell("<k>", intToToken(1))),
                KRewrite(cell("<k>", intToToken(2)), cells()))));
        Assert.assertEquals(expected, concretize(term));
    }

    @Test
    public void testThreeRewritesSplit() {
        K term = cell("<T>",
                KRewrite(cells(cell("<k>"),cell("<env>")), cells()),
                KRewrite(cell("<env>"), cell("<k>")),
                KRewrite(cell("<k>"), cell("<k>")));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", KRewrite(cells(cell("<k>"),cell("<env>")), cells())),
                cell("<t>", KRewrite(cell("<env>"), cell("<k>"))),
                cell("<t>", KRewrite(cell("<k>"), cell("<k>")))));
        Assert.assertEquals(expected, concretize(term));
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
