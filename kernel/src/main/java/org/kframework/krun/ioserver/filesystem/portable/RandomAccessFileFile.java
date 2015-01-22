// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.Arrays;

public class RandomAccessFileFile extends File {

    protected RandomAccessFile raf;

    public RandomAccessFileFile(RandomAccessFile raf) {
        this.raf = raf;
    }

    public long tell() throws IOException {
        try {
            return raf.getFilePointer();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
    }

    public void seek(long pos) throws IOException {
        try {
            raf.seek(pos);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }

    public void putc(byte b) throws IOException {
        try {
            raf.writeByte(b);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }

    public byte getc() throws IOException {
        try {
            return raf.readByte();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
            throw e; //unreachable
        }
    }

    public byte[] read(int n) throws IOException {
        int read;
        byte[] bytes;
        try {
            bytes = new byte[n];
            read = raf.read(bytes);
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
        try {
            raf.write(b);
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }

    void close() throws IOException {
        try {
            raf.close();
        } catch (IOException e) {
            PortableFileSystem.processIOException(e);
        }
    }
}
