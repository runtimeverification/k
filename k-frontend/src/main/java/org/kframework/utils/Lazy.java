// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils;

import java.io.Serializable;
import org.kframework.SerializableSupplier;

/**
 * A thread-safe lazy initialization wrapper. {@code private Foo computeFoo() { ... } private final
 * Lazy<Foo> lazyFoo = new Lazy<>(this::computeFoo); public Foo foo() { return lazyFoo.get(); } }
 */
public class Lazy<T> implements Serializable {
  private volatile T object;
  private final SerializableSupplier<T> supplier;

  public Lazy(SerializableSupplier<T> supplier) {
    this.supplier = supplier;
  }

  public T get() {
    T result = this.object;
    if (result == null) {
      synchronized (this) {
        result = this.object;
        if (result == null) {
          this.object = result = supplier.get();
        }
      }
    }
    return result;
  }
}
