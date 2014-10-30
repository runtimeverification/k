// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import org.junit.Test;
import static org.kframework.kore.Interface.*;

public class VisitorTest {
  class FooTransformer extends AbstractKORETransformer<K> {

    @Override
    public K transform(KApply k) {
      return k.copy();
    }

    @Override
    public K transform(KRewrite k) {
      return k.copy();
    }

    @Override
    public K transform(KToken k) {
      return KVariable("T");
    }

    @Override
    public K transform(KVariable k) {
      return k.copy();
    }
  }

  @Test
  public void testFoo() {
    FooTransformer fooTransformer = new FooTransformer();

    KToken someToken = KToken(Sort("foo"), KString("bla"));

    K transformed = fooTransformer.transform(someToken);

    System.out.println(transformed);
  }
}
