// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import java.util.Objects;
import org.kframework.kore.Sort;
import org.kframework.parser.ProductionReference;

/**
 * A class representing a particular usage of a production's parameter. Effectively, a pair
 * (ProductionReference, Sort) with reference semantics for the ProductionReference.
 */
public final class ParamId {
  private final ProductionReference pr;
  private final Sort param;

  public ParamId(ProductionReference pr, Sort param) {
    this.pr = pr;
    this.param = param;
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof ParamId p) {
      return this.pr == p.pr && this.param.equals(p.param);
    }
    return false;
  }

  @Override
  public int hashCode() {
    return Objects.hash(System.identityHashCode(pr), param);
  }
}
