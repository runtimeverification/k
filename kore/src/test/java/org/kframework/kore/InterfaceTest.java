// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore;

import org.junit.Test;
import org.kframework.builtin.Sorts;

import static org.junit.Assert.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

public class InterfaceTest {

    @Test
    public void example() {
        // Creating "A + 0 => A" programmatically

        KRewrite k = KRewrite(
                KApply(KLabel("_+_"), (K)KVariable("A"), (K)KToken("0", Sort("Int"))),
                KVariable("A"));

        // Navigating it
        KLabel theLabel = ((KApply) k.left()).klabel();
        theLabel.name();
    }

    @Test
    public void kListIsAssociative() {
        // assertEquals(KList(KToken(Sorts.Int(), "1"), KToken(Sorts.Int(), "2")), KList(KToken(Sorts.Int(), "1"), KList(KToken(Sorts.Int(), "2"))));
    }

    @Test
    public void manipulatingKList() {
        KList l = KList(Seq(KToken("1", Sorts.Int()), KToken("2", Sorts.Int()))).stream().map(x -> KToken("3", Sorts.Int())).collect(toKList());
        assertEquals(KList(Seq(KToken("3", Sorts.Int()), KToken("3", Sorts.Int()))), l);
    }

    @Test
    public void kSeqIsAssociative() {
        assertEquals(KSequence(Seq(KToken("1", Sorts.Int()), KToken("2", Sorts.Int()))), KSequence(Seq(KToken("1", Sorts.Int()), KSequence(Seq(KToken("2", Sorts.Int()))))));
    }

//    @Test
//    public void manipulatingKSeq() {
//        KSequence l = stream(KSequence(KToken("1", Sorts.Int()), KToken("2", Sorts.Int()))).map(x -> KToken("3", Sorts.Int())).collect(toKSequence());
//        assertEquals(KSequence(KToken("3", Sorts.Int()), KToken("3", Sorts.Int())), l);
//    }
}
