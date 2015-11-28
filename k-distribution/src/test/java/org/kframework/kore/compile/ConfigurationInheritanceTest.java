// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore.compile;

import org.junit.Test;
import org.kframework.utils.KoreUtils;

import java.net.URISyntaxException;

public class ConfigurationInheritanceTest {
    @Test
    public void simpleTest() throws URISyntaxException {
        String filename = "/compiler-tests/configuration-inheritance.k";
        KoreUtils utils = new KoreUtils(filename, "B", "B");
        System.out.println(utils.compiledDef.executionModule().sentences().mkString("\n"));
    }
}
