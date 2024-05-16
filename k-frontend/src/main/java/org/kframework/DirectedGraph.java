// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.apache.commons.lang3.tuple.Pair;

public class DirectedGraph {
  /** Topologically sort based on the provided edges, unless a cycle is present. */
  public static <T> Optional<Stream<T>> topologicalSort(Iterable<Pair<T, T>> edges) {
    Map<T, Set<T>> toPred = new HashMap<>();
    for (Pair<T, T> edge : edges) {
      if (!toPred.containsKey(edge.getLeft())) {
        toPred.put(edge.getLeft(), new HashSet<>());
      }
      if (!toPred.containsKey(edge.getRight())) {
        toPred.put(edge.getRight(), new HashSet<>());
      }
      toPred.get(edge.getRight()).add(edge.getLeft());
    }
    return topologicalSort(toPred, Stream.empty());
  }

  private static <T> Optional<Stream<T>> topologicalSort(Map<T, Set<T>> toPreds, Stream<T> done) {
    Map<Boolean, List<Map.Entry<T, Set<T>>>> partition =
        toPreds.entrySet().stream()
            .collect(Collectors.partitioningBy((e) -> e.getValue().isEmpty()));
    List<Map.Entry<T, Set<T>>> noPreds = partition.get(true);
    Map<T, Set<T>> hasPreds =
        partition.get(false).stream()
            .collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    if (noPreds.isEmpty()) {
      if (hasPreds.isEmpty()) {
        return Optional.of(done);
      }
      return Optional.empty();
    }
    Set<T> found = noPreds.stream().map(Map.Entry::getKey).collect(Collectors.toSet());
    for (Map.Entry<T, Set<T>> entry : hasPreds.entrySet()) {
      entry.getValue().removeAll(found);
    }
    return topologicalSort(hasPreds, Stream.concat(done, found.stream()));
  }

  /**
   * Find an inclusion-maximal set of mutually vertex-disjoint cycles. Note that the particular
   * cycles found depends on the iteration order of the input adjacency matrix.
   */
  public static <T> Stream<List<T>> findDisjointCycles(Map<T, Set<T>> deps) {
    Optional<List<T>> cycle = findCycle(deps);
    if (cycle.isEmpty()) {
      return Stream.empty();
    }
    Set<T> inCycle = new HashSet<>(cycle.get());
    Map<T, Set<T>> depsMinusCycle =
        deps.entrySet().stream()
            .filter(e -> !inCycle.contains(e.getKey()))
            .collect(
                Collectors.toMap(
                    Map.Entry::getKey,
                    e ->
                        e.getValue().stream()
                            .filter(t -> !inCycle.contains(t))
                            .collect(Collectors.toSet())));
    return Stream.concat(Stream.of(cycle.get()), findDisjointCycles(depsMinusCycle));
  }

  /**
   * Find a cycle in the graph if one exists. Note that the particular cycle found depends on the
   * iteration order of the provided adjacency matrix.
   */
  public static <T> Optional<List<T>> findCycle(Map<T, Set<T>> adjacency) {
    Set<T> visited = new HashSet<>();
    Set<T> onStack = new HashSet<>();
    Map<T, T> edgeTo = new HashMap<>();
    for (T elem : adjacency.keySet()) {
      if (!visited.contains(elem)) {
        Optional<List<T>> cycle = findCycle(adjacency, visited, onStack, edgeTo, elem);
        if (cycle.isPresent()) {
          return cycle;
        }
      }
    }
    return Optional.empty();
  }

  private static <T> Optional<List<T>> findCycle(
      Map<T, Set<T>> deps, Set<T> visited, Set<T> onStack, Map<T, T> edgeTo, T start) {
    visited.add(start);
    onStack.add(start);
    for (T next : deps.getOrDefault(start, Set.of())) {
      if (!visited.contains(next)) {
        edgeTo.put(next, start);
        Optional<List<T>> cycle = findCycle(deps, visited, onStack, edgeTo, next);
        if (cycle.isPresent()) {
          return cycle;
        }
        continue;
      }
      if (onStack.contains(next)) {
        List<T> cycle = new ArrayList<>();
        for (T elem = start; !elem.equals(next); elem = edgeTo.get(elem)) {
          cycle.add(elem);
        }
        cycle.add(next);
        Collections.reverse(cycle);
        return Optional.of(cycle);
      }
    }
    onStack.remove(start);
    return Optional.empty();
  }

  /** Rotate a cycle so that the least element is first. */
  public static <T> List<T> sortCycle(List<T> cycle, Comparator<T> comp) {
    Collections.rotate(cycle, -(cycle.indexOf(Collections.min(cycle, comp))));
    return cycle;
  }
}
