// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.apache.commons.lang3.tuple.Pair;

public class TopologicalSort {
  /** Topologically sort based on the provided edges, unless a cycle is present. */
  public static <T> Optional<Stream<T>> tsort(Iterable<Pair<T, T>> edges) {
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
    return tsortInternal(toPred, Stream.empty());
  }

  private static <T> Optional<Stream<T>> tsortInternal(Map<T, Set<T>> toPreds, Stream<T> done) {
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
    return tsortInternal(hasPreds, Stream.concat(done, found.stream()));
  }
}
