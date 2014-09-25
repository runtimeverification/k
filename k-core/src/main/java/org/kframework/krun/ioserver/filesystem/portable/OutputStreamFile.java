// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import java.io.IOException;
import java.io.FileOutputStream;

public class OutputStreamFile extends File {

    protected FileOutputStream os;

    public OutputStreamFile(FileOutputStream os) {
        this.os = os;
    }

    public long tell() throws IOException {
        // we can't just assume it's not possible: what if the stream points to a regular file and not a
        // pipe?
        try {
            return os.getChannel().position();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
    }

    public void seek(long pos) throws IOException {
        //see comment on tell
        try {
            os.getChannel().position(pos);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
    }

    public void putc(byte b) throws IOException {
        try {
            os.write(b);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }

    public byte getc() throws IOException {
        //since technically reading from file descriptors oen and two can succeed or fail depending
        //on what underlying file they point to and what mode they were opened in, we don't throw
        //an IOException here. An IOException in the api corresponds to a system call failing in a
        //well-defined fashion. Here we throw an UnsupportedOperationException because the behavior
        //is undefined.
        throw new UnsupportedOperationException();
    }

    public byte[] read(int n) throws IOException {
        //see comment on getc
        throw new UnsupportedOperationException();
    }

    public void write(byte[] b) throws IOException {
        try {
            os.write(b);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }

    void close() throws IOException {
        try {
            os.close();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }
}
