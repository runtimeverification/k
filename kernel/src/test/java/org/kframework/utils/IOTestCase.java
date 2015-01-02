// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.After;
import org.junit.Before;

public abstract class IOTestCase extends BaseTestCase {

    PrintStream oldOut, oldErr;
    protected ByteArrayOutputStream stdout = new ByteArrayOutputStream();
    protected ByteArrayOutputStream stderr = new ByteArrayOutputStream();

    @Before
    public void setUpIO() {
        oldOut = System.out;
        oldErr = System.err;
        System.setOut(new PrintStream(stdout));
        System.setErr(new PrintStream(stderr));
    }

    @After
    public void tearDownIO() {
        System.setOut(oldOut);
        System.setErr(oldErr);
    }
}
