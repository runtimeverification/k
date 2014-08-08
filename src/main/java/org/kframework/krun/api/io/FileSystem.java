// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api.io;

import java.io.IOException;

/**
The interface to the KRun file system API. Each implementation of this interface provides a set of functionality for manipulating files, whether real or virtual, on a file system.
*/
public interface FileSystem {

    /**
    Get the file object associated with a virtual file descriptor.
    @param fd The virtual file descriptor to obtain the file associated with.
    @return An object exposing IO operations on the file specified.
    @exception IOException Thrown if the file descriptor does not exist or is not open
    (errno EBADF).
    */
    public File get(long fd) throws IOException;

    /**
    Open a file at a specified path with a specified mode.
    @param path The relative or absolute path of the file.
    @param mode The mode to open the file in: one of 'r', 'w', 'rw'.
    @return The file descriptor
    @exception IllegalArgumentException Thrown if an invalid mode is specified.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public long open(String path, String mode) throws IOException;

    /**
    Closer a file descriptor.
    @param fd The file descriptor to close.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public void close(long fd) throws IOException;

    //TODO(dwightguth): getcwd, chdir, opendir, remove, rename, mkdir, stat, lstat
}
