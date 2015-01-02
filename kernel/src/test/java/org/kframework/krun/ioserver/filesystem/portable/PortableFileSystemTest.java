// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import static org.mockito.Mockito.*;

import org.junit.Assert;
import org.junit.Test;
import org.kframework.krun.api.io.File;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.file.FileUtil;
import org.mockito.Matchers;
import org.mockito.Mock;
import org.mockito.invocation.InvocationOnMock;
import org.mockito.stubbing.Answer;

import java.io.IOException;
import java.nio.charset.Charset;


public class PortableFileSystemTest extends BaseTestCase {

    @Mock
    FileUtil files;

    @Test
    public void testReadFile() throws Exception {
        when(files.resolveWorkingDirectory(Matchers.anyString())).thenAnswer(new Answer<java.io.File>() {
            @Override
            public java.io.File answer(InvocationOnMock invocation)
                    throws Throwable {
                return new java.io.File((String)invocation.getArguments()[0]);
            }
        });
        PortableFileSystem fs = new PortableFileSystem(kem, files);
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
