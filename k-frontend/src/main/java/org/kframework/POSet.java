// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework;

import java.io.Serializable;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.utils.Lazy;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.Empty;
import org.pcollections.PStack;

public class POSet<T> implements Serializable {
  private final Set<Pair<T, T>> directRelations;
  private final Map<T, Set<T>> directRelationsMap;
  private final Map<T, Set<T>> relations;

  @SafeVarargs
  public POSet(Pair<T, T>... directRelations) {
    this(Arrays.stream(directRelations).collect(Collectors.toSet()));
  }

  public POSet(scala.collection.Set<scala.Tuple2<T, T>> directRelations) {
    this(
        Collections.stream(directRelations)
            .map(t -> Pair.of(t._1, t._2))
            .collect(Collectors.toSet()));
  }

  public POSet(Set<Pair<T, T>> directRelations) {
    this.directRelations = directRelations;
    this.directRelationsMap = directRelationsMap(directRelations);
    this.relations = transitiveClosure(directRelationsMap);
  }

  private static <T> Map<T, Set<T>> directRelationsMap(Set<Pair<T, T>> directRelations) {
    return directRelations.stream()
        .collect(Collectors.groupingBy(Pair::getLeft))
        .entrySet()
        .stream()
        .collect(
            Collectors.toMap(
                Map.Entry::getKey,
                e -> e.getValue().stream().map(Pair::getRight).collect(Collectors.toSet())));
  }

  private Map<T, Set<T>> transitiveClosure(Map<T, Set<T>> relations) {
    boolean changed = false;
    Map<T, Set<T>> newRelations = new HashMap<>();
    for (Map.Entry<T, Set<T>> rel : relations.entrySet()) {
      T start = rel.getKey();
      Set<T> succ = rel.getValue();
      Set<T> newSucc =
          succ.stream()
              .flatMap(s -> relations.getOrDefault(s, new HashSet<>()).stream())
              .collect(Collectors.toSet());
      if (newSucc.contains(start)) {
        constructAndThrowCycleException(start, start, Empty.stack());
      }

      newSucc.addAll(succ);
      if (newSucc.size() > succ.size()) {
        changed = true;
      }
      newRelations.put(start, newSucc);
    }
    if (changed) {
      return transitiveClosure(newRelations);
    }
    return relations;
  }

  private void constructAndThrowCycleException(T start, T current, PStack<T> path) {
    PStack<T> currentPath = path.plus(current);
    Set<T> succs = directRelationsMap.getOrDefault(current, new HashSet<>());
    if (succs.contains(start)) {
      // we built the path in reverse, so use plusAll to reverse it back
      PStack<T> finalPath = Empty.<T>stack().plusAll(currentPath.plus(start));
      throw KEMException.compilerError(
          "Illegal circular relation: "
              + finalPath.stream().map(Object::toString).collect(Collectors.joining(" < ")));
    }
    succs.forEach(s -> constructAndThrowCycleException(start, s, currentPath));
  }

  public Map<T, Set<T>> relations() {
    return relations;
  }

  private Set<T> computeElements() {
    return directRelations.stream()
        .flatMap(p -> Stream.of(p.getLeft(), p.getRight()))
        .collect(Collectors.toSet());
  }

  private final Lazy<Set<T>> elementsLazy = new Lazy<>(this::computeElements);

  public Set<T> elements() {
    return elementsLazy.get();
  }

  private java.util.List<T> computeSortedElements() {
    Optional<Stream<T>> topological = DirectedGraph.topologicalSort(directRelations);
    // We already checked for cycles during construction, so the sort should succeed
    assert topological.isPresent();
    return topological.get().toList();
  }

  private final Lazy<java.util.List<T>> sortedElementsLazy =
      new Lazy<>(this::computeSortedElements);

  public java.util.List<T> sortedElements() {
    return sortedElementsLazy.get();
  }

  private Map<T, Set<T>> computeRelationsOp() {
    return relations.entrySet().stream()
        .flatMap(e -> e.getValue().stream().map(val -> Pair.of(val, e.getKey())))
        .collect(Collectors.groupingBy(Pair::getLeft))
        .entrySet()
        .stream()
        .collect(
            Collectors.toMap(
                Map.Entry::getKey,
                e -> e.getValue().stream().map(Pair::getRight).collect(Collectors.toSet())));
  }

  private final Lazy<Map<T, Set<T>>> relationsOpLazy = new Lazy<>(this::computeRelationsOp);

  public Map<T, Set<T>> relationsOp() {
    return relationsOpLazy.get();
  }

  private Set<T> computeMinimalElements() {
    return minimal(elements());
  }

  private final Lazy<Set<T>> minimalElementsLazy = new Lazy<>(this::computeMinimalElements);

  public Set<T> minimalElements() {
    return minimalElementsLazy.get();
  }

  private Set<T> computeMaximalElements() {
    return maximal(elements());
  }

  private final Lazy<Set<T>> maximalElementsLazy = new Lazy<>(this::computeMaximalElements);

  public Set<T> maximalElements() {
    return maximalElementsLazy.get();
  }

  private Optional<T> computeMinimum() {
    Set<T> minimalElems = minimalElements();
    if (minimalElems.size() == 1) {
      return Optional.of(minimalElems.iterator().next());
    }
    return Optional.empty();
  }

  private final Lazy<Optional<T>> minimumLazy = new Lazy<>(this::computeMinimum);

  public Optional<T> minimum() {
    return minimumLazy.get();
  }

  private Optional<T> computeMaximum() {
    Set<T> maximalElems = maximalElements();
    if (maximalElems.size() == 1) {
      return Optional.of(maximalElems.iterator().next());
    }
    return Optional.empty();
  }

  private final Lazy<Optional<T>> maximumLazy = new Lazy<>(this::computeMaximum);

  public Optional<T> maximum() {
    return maximumLazy.get();
  }

  private Map<T, Integer> computeConnectedComponents() {
    var data = new HashMap<T, Integer>();
    int nextComponent = 0;

    for (var node : elements()) {
      var queue = new ArrayDeque<T>();
      queue.push(node);

      var anyChange = false;
      while (!queue.isEmpty()) {
        var cur = queue.pop();
        if (data.containsKey(cur)) {
          continue;
        }

        data.put(cur, nextComponent);
        anyChange = true;

        for (var next : relations().getOrDefault(cur, Set.of())) {
          queue.addFirst(next);
        }

        for (var next : relationsOp().getOrDefault(cur, Set.of())) {
          queue.addFirst(next);
        }
      }

      if (anyChange) {
        nextComponent++;
      }
    }

    return data;
  }

  private final Lazy<Map<T, Integer>> connectedComponentsLazy =
      new Lazy<>(this::computeConnectedComponents);

  /**
   * Compute a connected component identifier for each element in this POSet.
   *
   * <p>Two elements share a connected component identifier if there is some sequence of edges (in
   * any direction) that connect them. Note that being in the same connected component does not
   * imply that two elements are related to one another in their POSet; if `A <: B` and `A <: C`
   * then `B` and `C` are in the same connected component but are not in any ordering relation with
   * each other.
   *
   * <p>Note that this mapping is computed lazily when this method is first called; it uses a DFS
   * over the POSet graph internally and has time complexity of `O(V + E)`. Subsequent calls will
   * not recompute the mapping and therefore take constant time.
   *
   * @return A lazily initialized map from elements to an integer in the range [0, N) indicating
   *     which connected component that element belongs to, where N is the number of connected
   *     components.
   */
  public Map<T, Integer> connectedComponents() {
    return connectedComponentsLazy.get();
  }

  public boolean lessThan(T x, T y) {
    return relations.getOrDefault(x, Set.of()).contains(y);
  }

  public boolean lessThanEq(T x, T y) {
    return x.equals(y) || lessThan(x, y);
  }

  public boolean directlyLessThan(T x, T y) {
    return directRelationsMap.getOrDefault(x, Set.of()).contains(y);
  }

  public boolean greaterThan(T x, T y) {
    return relations.getOrDefault(y, Set.of()).contains(x);
  }

  public boolean greaterThanEq(T x, T y) {
    return x.equals(y) || greaterThan(x, y);
  }

  public boolean directlyGreaterThan(T x, T y) {
    return directRelationsMap.getOrDefault(y, Set.of()).contains(x);
  }

  public boolean inSomeRelation(T x, T y) {
    return lessThan(x, y) || greaterThan(x, y);
  }

  public boolean inSomeRelationEq(T x, T y) {
    return x.equals(y) || inSomeRelation(x, y);
  }

  private enum BoundType {
    UPPER,
    LOWER
  }

  private Set<T> bounds(BoundType boundType, Iterable<T> elems) {
    Map<T, Set<T>> relationsOrRelationsOp =
        switch (boundType) {
          case UPPER -> relations;
          case LOWER -> relationsOp();
        };
    return Collections.streamIter(elems)
        .map(
            e -> {
              Set<T> bounds = new HashSet<>(relationsOrRelationsOp.getOrDefault(e, Set.of()));
              bounds.add(e);
              return bounds;
            })
        .reduce(
            (a, b) -> {
              a.retainAll(b);
              return a;
            })
        .orElse(elements());
  }

  public Set<T> upperBounds(Iterable<T> elems) {
    return bounds(BoundType.UPPER, elems);
  }

  public Set<T> lowerBounds(Iterable<T> elems) {
    return bounds(BoundType.LOWER, elems);
  }

  public Set<T> minimal(Iterable<T> elems) {
    return Collections.streamIter(elems)
        .filter(s1 -> Collections.streamIter(elems).noneMatch(s2 -> greaterThan(s1, s2)))
        .collect(Collectors.toSet());
  }

  public Set<T> maximal(Iterable<T> elems) {
    return Collections.streamIter(elems)
        .filter(s1 -> Collections.streamIter(elems).noneMatch(s2 -> lessThan(s1, s2)))
        .collect(Collectors.toSet());
  }

  public Comparator<T> asComparator() {
    return (T x, T y) -> lessThan(x, y) ? -1 : (greaterThan(x, y) ? 1 : 0);
  }

  @Override
  public String toString() {
    return "POSet("
        + relations.entrySet().stream()
            .flatMap(e -> e.getValue().stream().map(val -> e.getKey() + "<" + val))
            .collect(Collectors.joining(","))
        + ")";
  }

  @Override
  public int hashCode() {
    return relations.hashCode();
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof POSet<?> po) {
      return relations.equals(po.relations);
    }
    return false;
  }
}
