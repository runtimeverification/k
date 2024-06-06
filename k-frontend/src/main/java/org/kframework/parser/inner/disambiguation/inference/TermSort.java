// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import org.kframework.parser.Term;

/**
 * The sort of a Term and all its variables.
 *
 * @param term - The term which has this particular sort
 * @param sort - The top level sort of the overall term
 * @param varSorts - The sort of each variable occurring in the term
 * @param <S> The particular type of sort we are considering (will be BoundedSort, CompactSort, and
 *     Sort depending on the stage of inference).
 */
public record TermSort<S>(Term term, S sort, Map<VariableId, ? extends S> varSorts) {
  /**
   * Map over all contained sorts in their polarity.
   *
   * @param func - A map taking both a sort and a polarity then producing a new sort.
   */
  public <T> TermSort<T> mapSorts(BiFunction<? super S, Boolean, ? extends T> func) {
    T newSort = func.apply(sort, true);
    Map<VariableId, ? extends T> newVarSorts =
        varSorts().entrySet().stream()
            .collect(Collectors.toMap((Map.Entry::getKey), (e) -> func.apply(e.getValue(), false)));
    return new TermSort<>(term, newSort, newVarSorts);
  }

  /** Apply an action to all contained sorts in their polarity. */
  public void forEachSort(BiConsumer<? super S, Boolean> action) {
    action.accept(sort, true);
    varSorts().values().forEach((v) -> action.accept(v, false));
  }
}
