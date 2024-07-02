// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;

import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.VisitK;
import scala.Tuple2;

public class ComputeTransitiveFunctionDependencies {
  public ComputeTransitiveFunctionDependencies(Module module) {
    dependencies = new DirectedSparseGraph<>();

    Set<KLabel> anywhereKLabels = new HashSet<>();
    stream(module.rules())
        .filter(r -> !ExpandMacros.isMacro(r))
        .forEach(
            r -> {
              K left = RewriteToTop.toLeft(r.body());
              if (left instanceof KApply kapp) {
                if (r.att().contains(Att.ANYWHERE())) {
                  if (kapp.klabel().name().equals(KLabels.INJ)) {
                    K k = kapp.items().get(0);
                    if (k instanceof KApply) {
                      anywhereKLabels.add(((KApply) k).klabel());
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
        if (module.attributesFor().getOrElse(k.klabel(), () -> Att.empty()).contains(Att.FUNCTION())
            || anywhereKLabels.contains(k.klabel())) {
          dependencies.addEdge(new Object(), current, k.klabel());
        }
        super.apply(k);
      }
    }

    for (Tuple2<KLabel, scala.collection.immutable.Set<Rule>> entry : iterable(module.rulesFor())) {
      for (Rule rule : iterable(entry._2())) {
        if (module
            .attributesFor()
            .getOrElse(entry._1(), () -> Att.empty())
            .contains(Att.FUNCTION())) {
          GetPredecessors visitor = new GetPredecessors(entry._1());
          visitor.apply(rule.body());
          visitor.apply(rule.requires());
        }
      }
    }
  }

  private static <V> Set<V> ancestors(
      Collection<? extends V> startNodes, DirectedGraph<V, ?> graph) {
    Queue<V> queue = new LinkedList<V>();
    queue.addAll(startNodes);
    Set<V> visited = new LinkedHashSet<V>(startNodes);
    while (!queue.isEmpty()) {
      V v = queue.poll();
      Collection<V> neighbors = graph.getPredecessors(v);
      for (V n : neighbors) {
        if (!visited.contains(n)) {
          queue.offer(n);
          visited.add(n);
        }
      }
    }
    return visited;
  }

  public Set<KLabel> ancestors(Set<KLabel> labels) {
    return ancestors(labels, dependencies);
  }

  private final DirectedGraph<KLabel, Object> dependencies;
}
