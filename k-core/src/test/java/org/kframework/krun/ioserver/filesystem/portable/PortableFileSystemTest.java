// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import org.junit.Assert;
import org.junit.Test;
import org.kframework.krun.api.io.File;

import java.io.IOException;
import java.nio.charset.Charset;


public class PortableFileSystemTest {

    @Test
    public void testReadFile() throws Exception {
        PortableFileSystem fs = new PortableFileSystem();
        long fd = fs.open(new java.io.File(getClass().getResource("/fs-test.txt").toURI()).getAbsolutePath(), "r");
        File f = fs.get(fd);
        byte[] file = "foo\n".getBytes(Charset.forName("ASCII"));
        Assert.assertArrayEquals(file, f.read(4));
        try {
            f.read(1);
            Assert.fail();
        } catch (IOException e) {
            Assert.assertEquals("EOF", e.getMessage());
        }
    }

}
