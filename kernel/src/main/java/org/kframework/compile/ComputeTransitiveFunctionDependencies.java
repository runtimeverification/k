// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.KApply;
import org.kframework.kore.VisitK;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import scala.Tuple2;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import static org.kframework.Collections.*;

public class ComputeTransitiveFunctionDependencies {
    public ComputeTransitiveFunctionDependencies(Module module) {
        dependencies = new DirectedSparseGraph<>();

        Set<KLabel> anywhereKLabels = new HashSet<>();
        stream(module.rules()).filter(r -> !ExpandMacros.isMacro(r)).forEach(r -> {
            K left = RewriteToTop.toLeft(r.body());
            if (left instanceof KApply) {
                KApply kapp = (KApply) left;
                if (r.att().contains(Attribute.ANYWHERE_KEY)) {
                    if (kapp.klabel().name().equals(KLabels.INJ)) {
                        K k = kapp.items().get(0);
                        if (k instanceof KApply) {
                            anywhereKLabels.add(((KApply)k).klabel());
                        }
                    } else {
                        anywhereKLabels.add(kapp.klabel());
                    }
                }
            }
        });

        class GetPredecessors extends VisitK {
            private final KLabel current;

            private GetPredecessors(KLabel current) {
                this.current = current;
            }

            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals(KLabels.INJ)) {
                    super.apply(k);
                    return;
                }
                if (module.attributesFor().getOrElse(k.klabel(), () -> Att.empty()).contains(Attribute.FUNCTION_KEY) || anywhereKLabels.contains(k.klabel())) {
                    dependencies.addEdge(new Object(), current, k.klabel());
                }
                super.apply(k);
            }
        }

        for (Tuple2<KLabel, scala.collection.Set<Rule>> entry : iterable(module.rulesFor())) {
            for (Rule rule : iterable(entry._2())) {
                if (module.attributesFor().getOrElse(entry._1(), () -> Att.empty()).contains(Attribute.FUNCTION_KEY)) {
                    GetPredecessors visitor = new GetPredecessors(entry._1());
                    visitor.apply(rule.body());
                    visitor.apply(rule.requires());
                }
            }
        }
    }

    private static <V> Set<V> ancestors(
            Collection<? extends V> startNodes, DirectedGraph<V, ?> graph)
    {
        Queue<V> queue = new LinkedList<V>();
        queue.addAll(startNodes);
        Set<V> visited = new LinkedHashSet<V>(startNodes);
        while(!queue.isEmpty())
        {
            V v = queue.poll();
            Collection<V> neighbors = graph.getPredecessors(v);
            for (V n : neighbors)
            {
                if (!visited.contains(n))
                {
                    queue.offer(n);
                    visited.add(n);
                }
            }
        }
        return visited;
    }

    public Set<KLabel> ancestors(KLabel label) {
        return ancestors(Collections.singleton(label), dependencies);
    }

    public Set<KLabel> ancestors(Set<KLabel> labels) {
        return ancestors(labels, dependencies);
    }

    private DirectedGraph<KLabel, Object> dependencies;
}
