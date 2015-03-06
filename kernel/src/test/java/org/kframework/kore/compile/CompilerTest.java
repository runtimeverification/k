package org.kframework.kore.compile;


import com.google.common.base.Function;
import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import org.junit.Assert;
import org.junit.Test;
import org.kframework.kore.*;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

public class CompilerTest {

    static class Configuration {

        Map<KLabel, Integer> levels = new HashMap();
        Map<KLabel, KLabel> parents = new HashMap();

        Configuration() {
            levels.put(KLabel("<k>"), 3);
            levels.put(KLabel("<env>"), 3);
            levels.put(KLabel("<t>"), 2);
            levels.put(KLabel("<ts>"), 1);
            levels.put(KLabel("<state>"), 1);
            levels.put(KLabel("<T>"), 0);

            parents.put(KLabel("<k>"), KLabel("<t>"));
            parents.put(KLabel("<env>"), KLabel("<t>"));
            parents.put(KLabel("<t>"), KLabel("<ts>"));
            parents.put(KLabel("<ts>"), KLabel("<T>"));
            parents.put(KLabel("<state>"), KLabel("<T>"));
        }

        Comparator<KLabel> comparator() {
            return (k1, k2) -> levels.get(k2) - levels.get(k1);
        }

        int getLevel(KLabel k) {
            return levels.get(k);
        }

        KLabel getParent(KLabel k) {
            return parents.get(k);
        }
    }

    final Configuration cfg = new Configuration();

    K concretize(K k) {
        if (k instanceof KApply) {
            KApply app = (KApply)k;
            KLabel target = app.klabel();
            TreeMap<Integer, List<K>>
            ListMultimap<Integer, K> levels = Multimaps.newListMultimap(new TreeMap<Integer, >)
            List<K> finishedChildren = new ArrayList<K>();
            int maxLevel = 0;
            for (K child : app.klist().items()) {
                if (child instanceof KApply) {
                    KLabel parent = cfg.getParent(((KApply) child).klabel());
                    if (parent != null && !parent.equals(target)) {
                        int level = cfg.getLevel(((KApply) child).klabel());
                        if (level > maxLevel) { maxLevel = level; }
                        levels.put(level, child);
                    }
                }
                finishedChildren.add(child);
            }
            while (maxLevel )
            levels.keys().
            Multimaps.index(k -> cfg.get)
            List<K> nonCellChildren = app.klist().stream()
                    .filter()
            Stream<K> children = ((KApply) k).klist().stream();
            KLabel klabel = ((KApply) k).klabel();
            TreeSet<K> toProcess = new TreeSet<>();
            Set<K> processed = new HashSet<>();

            children.forEach(k -> {
                if (k instanceof KApply)
                    if (cfg.getParent(((KApply) k).klabel()).equals(klabel))
                        else

                    else

            });

            List<K> sortedChildren = children.sorted(Comparator.comparing(kk -> ((KApply) kk).klabel(), cfg.comparator())).collect(Collectors.toList());

            sortedChildren.filter();
        }
        return k;
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

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }
}
