// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.junit.Test;
import org.kframework.utils.errorsystem.KExceptionManager;

public class KRunFrontEndTest {

    @Test(expected=KExceptionManager.KEMException.class)
    public void testInvalidArguments() {
        org.kframework.krun.KRunFrontEnd.execute_Krun(new String[] {"--backend", "foobarbaz"});
    }
}
