package org.kframework.krun.ioserver.filesystem.portable;

import java.io.IOException;
import java.io.OutputStream;

public class OutputStreamFile extends File {

    protected OutputStream os;

    public OutputStreamFile(OutputStream os) {
        this.os = os;
    }

    public long tell() throws IOException {
        throw new IOException("ESPIPE");
    }

    public void seek(long pos) throws IOException {
        throw new IOException("ESPIPE");
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
