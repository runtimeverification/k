// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import java.io.IOException;

public abstract class File implements org.kframework.krun.api.io.File {

    public abstract long tell() throws IOException;
    public abstract void seek(long pos) throws IOException;
    public abstract void putc(byte b) throws IOException;
    public abstract byte getc() throws IOException;
    public abstract byte[] read(int n) throws IOException;
    public abstract void write(byte[] b) throws IOException;

    abstract void close() throws IOException;
}
