package org.kframework.parser.inner.disambiguation.inference;

import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.stream.Collectors;
import org.kframework.parser.Term;

public record TermSort<S>(Term term, S sort, Map<VariableId, ? extends S> varSorts) {
  public <T> TermSort<T> mapSorts(BiFunction<? super S, Boolean, ? extends T> func) {
    T newSort = func.apply(sort, true);
    Map<VariableId, ? extends T> newVarSorts =
        varSorts().entrySet().stream()
            .collect(Collectors.toMap((Map.Entry::getKey), (e) -> func.apply(e.getValue(), false)));
    return new TermSort<>(term, newSort, newVarSorts);
  }

  public void forEachSort(BiConsumer<? super S, Boolean> action) {
    action.accept(sort, true);
    varSorts().values().forEach((v) -> action.accept(v, false));
  }
}
