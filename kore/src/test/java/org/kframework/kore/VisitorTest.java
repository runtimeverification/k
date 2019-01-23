// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.kore;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;

import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;

public class VisitorTest {
    class FooTransformer extends TransformK {

        @Override
        public K apply(KToken k) {
            return KVariable("T");
        }

        @Override
        public K apply(KVariable k) {
            return k;
        }

        @Override
        public K apply(KSequence k) {
            List<K> newItems = k.items().stream().map(this).collect(Collectors.toList());
            return KORE.KSequence(newItems, k.att());
        }

        @Override
        public K apply(InjectedKLabel k) {
            return k;
        }

    }

    @Test
    public void testTopLevel() {
        FooTransformer fooTransformer = new FooTransformer();
        K t = fooTransformer.apply(KToken("bla", Sort("foo")));

        assertEquals(KVariable("T"), t);
    }

    @Test
    public void testTopLevelNoTransoformation() {
        FooTransformer fooTransformer = new FooTransformer();
        KVariable term = KVariable("X");
        K t = fooTransformer.apply(term);

        assertEquals(term, t);
    }

    @Test
    public void testGenericK() {
        FooTransformer fooTransformer = new FooTransformer();
        K term = KVariable("X");
        K t = fooTransformer.apply(term);

        assertEquals(term, t);
    }

    @Test
    public void testTopLevelNoTransoformationOnCollection() {
        FooTransformer fooTransformer = new FooTransformer();
        KRewrite term = KRewrite(KVariable("X"), KVariable("Y"));
        KRewrite t = (KRewrite) fooTransformer.apply(term);

        assertEquals(term, t);
    }

    @Test
    public void testNested() {
        FooTransformer fooTransformer = new FooTransformer();
        KRewrite t = (KRewrite) fooTransformer.apply(KRewrite(KToken("bla", Sort("foo")),
                KVariable("U")));

        assertEquals(KRewrite(KVariable("T"), KVariable("U")), t);
    }
}
