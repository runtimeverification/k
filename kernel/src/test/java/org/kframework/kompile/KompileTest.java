// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kompile;

import org.junit.Test;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.File;

public class KompileTest {

    KExceptionManager kem = new KExceptionManager(new GlobalOptions());

    @Test
    public void simpleTest() {

    }

    protected void test(File definitionFile, String mainModuleName, String mainSyntaxModuleName) {
//        Kompile.apply(definitionFile, mainModuleName, mainSyntaxModuleName, kem);
    }
}
