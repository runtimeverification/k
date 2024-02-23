// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.attributes;

import java.util.Objects;
import java.util.Optional;
import org.pcollections.HashPMap;

public class ClassSet<U> {

  public final HashPMap<Class<? extends U>, Object> data;

  private ClassSet(HashPMap<Class<? extends U>, Object> data) {
    this.data = data;
  }

  public <T extends U> ClassSet<U> add(Class<T> elemClass, T elem) {
    return new ClassSet<>(data.plus(elemClass, elem));
  }

  public <T extends U> Optional<T> get(Class<T> elemClass) {
    if (!data.containsKey(elemClass)) {
      return Optional.empty();
    }
    return Optional.of(Objects.requireNonNull(elemClass.cast(data.get(elemClass))));
  }

  public <T extends U> boolean contains(Class<T> elemClass) {
    return data.containsKey(elemClass);
  }

  public <T extends U> ClassSet<U> remove(Class<T> elemClass) {
    return new ClassSet<>(data.minus(elemClass));
  }
}
