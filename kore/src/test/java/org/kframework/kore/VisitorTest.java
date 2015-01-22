// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore;

import static org.junit.Assert.*;
import static org.kframework.kore.Constructors.*;

import org.junit.Test;

public class VisitorTest {
    class FooTransformer extends AbstractKORETransformer<K> {

        @Override
        public K apply(KApply k) {
            return (K) k.map(this);
        }

        @Override
        public K apply(KRewrite k) {
            return KRewrite(apply(k.left()), apply(k.right()), k.att());
        }

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
            return (K) k.map(this);
        }
    }

    @Test
    public void testTopLevel() {
        FooTransformer fooTransformer = new FooTransformer();
        K t = fooTransformer.apply(KToken(Sort("foo"), "bla"));

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
        KRewrite t = (KRewrite) fooTransformer.apply(KRewrite(KToken(Sort("foo"), "bla"),
                KVariable("U")));

        assertEquals(KRewrite(KVariable("T"), KVariable("U")), t);
    }
}
