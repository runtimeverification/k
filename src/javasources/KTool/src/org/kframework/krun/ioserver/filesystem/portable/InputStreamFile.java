// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;

public class InputStreamFile extends File {

    protected FileInputStream is;

    public InputStreamFile(FileInputStream is) {
        this.is = is;
    }

    public long tell() throws IOException {
        // we can't just assume it's not possible: what if stdin points to a regular file and not a
        // pipe?
        try {
            return is.getChannel().position();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
    }

    public void seek(long pos) throws IOException {
        //see comment on tell
        try {
            is.getChannel().position(pos);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
    }

    public void putc(byte b) throws IOException {
        //since technically writing to file descriptor zero can succeed or fail depending on what
        //underlying file it points to and what mode it was opened in, we don't throw an
        //IOException here. An IOException in the api corresponds to a system call failing in a
        //well-defined fashion. Here we throw an UnsupportedOperationException because the behavior
        //is undefined.
        throw new UnsupportedOperationException();
    }

    public byte getc() throws IOException {
        int read;
        try {
            read = is.read();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
        if (read == -1) {
            throw new IOException("EOF");
        }
        return (byte)read;
    }

    public byte[] read(int n) throws IOException {
        int read;
        byte[] bytes;
        try {
            bytes = new byte[n];
            read = is.read(bytes);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
        if (read == -1) {
            throw new IOException("EOF");
        }
        return Arrays.copyOfRange(bytes, 0, read);
    }

    public void write(byte[] b) throws IOException {
        //see comment on putc
        throw new UnsupportedOperationException();
    }

    void close() throws IOException {
        try {
            is.close();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }
}
