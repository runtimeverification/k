package org.kframework.kore.compile;


import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.kore.*;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.kore.KORE.*;

public class CompilerTest {

    static class Configuration {

        Map<KLabel, Integer> levels = new HashMap();
        Map<KLabel, KLabel> parents = new HashMap();
        Multimap<KLabel, KLabel> children = HashMultimap.create();
        public enum Multiplicity { ONE, OPTIONAL, STAR };
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
            addCell(null, "<T>",0,Multiplicity.ONE);
            addCell("<T>","<ts>",1,Multiplicity.ONE);
            addCell("<T>","<state>",1,Multiplicity.ONE);
            addCell("<ts>","<t>",2,Multiplicity.STAR);
            addCell("<ts>","<scheduler>",2,Multiplicity.ONE);
            addCell("<t>","<k>",3,Multiplicity.ONE);
            addCell("<t>","<env>",3,Multiplicity.ONE);
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

    List<KApply> makeParents(KLabel parent, List<KApply> children) {
        Map<KLabel, Long> counts =
           children.stream().map(KApply::klabel).filter(l -> cfg.getMultiplicity(l) != Configuration.Multiplicity.STAR)
                .collect(Collectors.groupingBy(k -> k, Collectors.counting()));
        if (counts.values().stream().anyMatch(repetitions -> repetitions > 1)) {
            if (counts.size() > 1) {
                throw new IllegalArgumentException("Ambiguous completion");
            } else {
                return children.stream().map(k -> KApply(parent,k)).collect(Collectors.toList());
            }
        } else {
            return Lists.newArrayList(KApply(parent, KList(children)));
        }
    }

    K concretize(K k) {
        if (!(k instanceof KApply)) {
            return k;
        } else {
            KApply app = (KApply)k;
            KLabel target = app.klabel();
            if (cfg.isLeafCell(target)) {
                return k;
            }
            List<KApply> children = app.klist().stream().map(kk -> (KApply)kk).collect(Collectors.toList());
            int targetLevel = cfg.getLevel(target)+1;
            TreeMap<Integer, List<KApply>> levels =
                    new TreeMap(children.stream().collect(Collectors.groupingBy(kk -> cfg.getLevel(kk.klabel()))));
            while (levels.lastKey() > targetLevel) {
                List<KApply> level = levels.remove(levels.lastKey());
                for (Map.Entry<KLabel,List<KApply>> e : level.stream().collect(Collectors.groupingBy(kk -> cfg.getParent(kk.klabel()))).entrySet()) {
                    KLabel parent = e.getKey();
                    List<KApply> newCells = makeParents(parent, e.getValue());
                    levels.compute(cfg.getLevel(parent),
                            (kk, v) -> { if (v == null) { return newCells; } else {v.addAll(newCells); return v;}});
                }
            }
            List<KApply> wrappedChildren = levels.remove(levels.lastKey());
            return KApply(target, KList(wrappedChildren));
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

    @Test public void testMultiplicitySeparate() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(1))),
                                  cell("<t>", cell("<k>", intToToken(2))));
        Assert.assertEquals(expected, concretize(term));
    }
    @Test public void testMultiplicityShared() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<env>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(1)), cell("<env>", intToToken(2))));
        Assert.assertEquals(expected, concretize(term));
    }
    @Test(expected = IllegalArgumentException.class) public void testAmbiguityError() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)), cell("<env>", intToToken(2)));
        concretize(term);
    }
    @Test public void testDeep2() {
        Assert.assertEquals(Lists.newArrayList(cell("<ts>", cell("<t>", intToToken(1)), cell("<t>", intToToken(2)))),
                makeParents(KLabel("<ts>"), Lists.newArrayList(cell("<t>", intToToken(1)), cell("<t>", intToToken(2)))));
    }
    @Test public void testDeep() {
        K term = cell("<T>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<T>", cell("<ts>", cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", cell("<k>", intToToken(2)))));
        Assert.assertEquals(expected, concretize(term));
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }
}
