// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;

import org.kframework.utils.errorsystem.KExceptionManager;

public class InputStreamFile extends File {

    protected InputStream is;

    private final KExceptionManager kem;

    public InputStreamFile(InputStream is, KExceptionManager kem) {
        this.is = is;
        this.kem = kem;
    }

    public long tell() throws IOException {
        kem.registerInternalWarning("Potentially unsound file system behavior: attempting to tell from "
                + "stdin. If you are interested in this behavior, please "
                + "file an issue on github.");
        throw new IOException("ESPIPE");
        // technically the above code is incorrect (it should be what is below); however,
        // we cannot guarantee in a client/server architecture that we have access to
        // the original file descriptors of the client, so we can't actually support this
        // behavior. Since it is a quite minor use case, I elected to log an error
        // informing the user of the unsupported behavior rather than trying to fix it,
        // a solution that would likely require changes to third-party C code.
//        try {
//            return is.getChannel().position();
//        } catch (IOException e) {
//            PortableFileSystem.processIOException(e);
//            throw e; //unreachable
//        }
    }

    public void seek(long pos) throws IOException {
        kem.registerInternalWarning("Potentially unsound file system behavior: attempting to seek from "
            + "stdin. If you are interested in this behavior, please "
            + "file an issue on github.");
        throw new IOException("ESPIPE");
        //see comment on tell
//        try {
//            is.getChannel().position(pos);
//        } catch (IOException e) {
//            PortableFileSystem.processIOException(e);
//            throw e; //unreachable
//        }
    }

    public void putc(byte b) throws IOException {
        //since technically writing to file descriptor zero can succeed or fail depending on what
        //underlying file it points to and what mode it was opened in, we don't throw an
        //IOException here. An IOException in the api corresponds to a system call failing in a
        //well-defined fashion. Here we throw an error because the behavior
        //is undefined.
        kem.registerInternalWarning("Unsupported file system behavior: tried to write to stdin."
                + " If you are interested in this behavior, please file an issue on github.");
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
        kem.registerInternalWarning("Unsupported file system behavior: tried to write to stdin."
                + " If you are interested in this behavior, please file an issue on github.");
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
