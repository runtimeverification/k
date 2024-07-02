// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore;

import org.kframework.Collections;
import scala.collection.Set;

/** Finds all patterns described by the visitor */
public class FindK extends AbstractFoldK<Set<K>> {
  @Override
  public Set<K> unit() {
    return Collections.Set();
  }

  @Override
  public Set<K> merge(Set<K> a, Set<K> b) {
    return a.$bar(b);
  }
}
