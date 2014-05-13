// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.filesystem.portable;

import org.apache.commons.collections15.BidiMap;
import org.apache.commons.collections15.bidimap.DualHashBidiMap;
import org.kframework.krun.api.io.File;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.io.EOFException;
import java.io.FileDescriptor;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.HashMap;
import java.util.Map;

public class PortableFileSystem implements FileSystem {

    private BidiMap<Long, FileDescriptor> descriptors = new DualHashBidiMap<Long, FileDescriptor>();

    private Map<FileDescriptor, File> files = new HashMap<FileDescriptor, File>();

    public PortableFileSystem() {
        descriptors.put(0L, FileDescriptor.in);
        descriptors.put(1L, FileDescriptor.out);
        descriptors.put(2L, FileDescriptor.err);
        files.put(FileDescriptor.in, new InputStreamFile(new FileInputStream(FileDescriptor.in)));
        files.put(FileDescriptor.out, new OutputStreamFile(new FileOutputStream(FileDescriptor.out)));
        files.put(FileDescriptor.err, new OutputStreamFile(new FileOutputStream(FileDescriptor.err)));
    }

    public File get(long fd) throws IOException {
        FileDescriptor fdObj = descriptors.get(fd);
        if (fdObj == null)
            throw new IOException("EBADF");
        File f = files.get(fdObj);
        if (f == null)
            throw new IOException("EBADF");
        return f;
    }

    private long fdCounter = 3;

    public long open(String path, String mode) throws IOException {
        if (!("r".equals(mode) || "w".equals(mode) || "rw".equals(mode))) {
            throw new IllegalArgumentException();
        }
        try {
            FileDescriptor fileFD;
            File file;
            if (mode.equals("w")) {
                FileOutputStream f = new FileOutputStream(path);
                fileFD = f.getFD();
                file = new OutputStreamFile(f);
            } else {
                RandomAccessFile f = new RandomAccessFile(path, mode);
                fileFD = f.getFD();
                file = new RandomAccessFileFile(f);
            }
            long fd = fdCounter++;
            descriptors.put(fd, fileFD);
            files.put(fileFD, file);
            return fd;
        } catch (FileNotFoundException e) {
            try {
                processFileNotFoundException(e);
            } catch (IOException ioe) {
                if (ioe.getMessage().equals("EISDIR") && mode.equals("r")) {
                    //man 2 open says you can open a directory in readonly mode with open, but
                    //java has no support for it. So we throw an UnsupportedOperationException
                    //instead of failing with EISDIR
                    throw new UnsupportedOperationException();
                }
                throw ioe;
            }
            throw e; //unreachable
        }
    }

    public void close(long fd) throws IOException {
        File f = get(fd);
        assert f instanceof org.kframework.krun.ioserver.filesystem.portable.File;
        ((org.kframework.krun.ioserver.filesystem.portable.File)f).close();
        files.remove(descriptors.get(fd));
        descriptors.remove(fd);
    }

    static void processFileNotFoundException(FileNotFoundException e) throws IOException {
        String message = e.getMessage();
        int startIdx = message.lastIndexOf("(") + 1;
        int endIdx = message.length() - 1;
        String realMessage = message.substring(startIdx, endIdx);
        processErrno(realMessage, e);
    }

    static void processErrno(String realMessage, IOException e) throws IOException {
        if (realMessage.equals("Permission denied")) {
            throw new IOException("EACCES");
        } else if (realMessage.equals("Is a directory")) {
            throw new IOException("EISDIR");
        } else if (realMessage.equals("Too many levels of symbolic links")) {
            throw new IOException("ELOOP");
        } else if (realMessage.equals("File name too long")) {
            throw new IOException("ENAMETOOLONG");
        } else if (realMessage.equals("No such file or directory")) {
            throw new IOException("ENOENT");
        } else if (realMessage.equals("Not a directory")) {
            throw new IOException("ENOTDIR");
        } else if (realMessage.equals("Negative seek offset")) {
            throw new IOException("EINVAL");
        } else if (realMessage.equals("Invalid argument")) {
            throw new IOException("EINVAL");
        } else if (realMessage.equals("Bad file descriptor")) {
            throw new IOException("EBADF");
        } else if (realMessage.equals("Illegal seek")) {
            throw new IOException("ESPIPE");
        }
        e.printStackTrace();
        GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
            KExceptionGroup.CRITICAL,
            "Unrecognized OS errno. Please file an issue on the K framework issue tracker\n" +
            "explaining precisely what you were trying to do and include the above stack trace"));
    }

    static void processIOException(IOException e) throws IOException {
        if (e instanceof EOFException) {
            throw new IOException("EOF");
        }
        processErrno(e.getMessage(), e);
    }
}
