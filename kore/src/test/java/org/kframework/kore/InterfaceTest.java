// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore;

import org.junit.Test;
import static org.junit.Assert.*;
import static org.kframework.kore.Constructors.*;

public class InterfaceTest {

    @Test
    public void example() {
        // Creating "A + 0 => A" programmatically

        KRewrite k = KRewrite(
                KApply(KLabel("_+_"),
                        KList(KVariable("A"), KToken(Sort("Int"), KString("0")))),
                KVariable("A"));

        // Navigating it
        KLabel theLabel = ((KApply) k.left()).klabel();
        theLabel.name();
    }
    
    @Test 
    public void kListIsAssociative() {        
        assertEquals(KList(KInt(1), KInt(2)), KList(KInt(1), KList(KInt(2))));
    }
    
    @Test 
    public void manipulatingKList() {
        KList l = stream(KList(KInt(1), KInt(2))).map(x -> KInt(3)).collect(toKList());
        assertEquals(KList(KInt(3), KInt(3)), l);
    }
}
