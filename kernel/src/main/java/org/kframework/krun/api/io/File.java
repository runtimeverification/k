// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api.io;

import java.io.IOException;

/**
The interface to a file in the KRun file system API. Each implementation of this interface provides a subset of the functionality of a random access file, based on what functionality the underlying file supports.
*/
public interface File {

    /**
    Get the location of the file pointer in the file.
    @return The number of bytes after the beginning of the file that the file pointer is at.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public long tell() throws IOException;

    /**
    Set the location of the file pointer in the file.
    @param pos The number of bytes after the beginning of the file that the file pointer is to be set.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public void seek(long pos) throws IOException;

    /**
    Write a byte to the file.
    @param b The byte to write.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public void putc(byte b) throws IOException;

    /**
    Get a byte from the file.
    @return The byte read.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public byte getc() throws IOException;

    /**
    Get a number of bytes from the file.
    @param n The number of bytes to read.
    @return The bytes read, possibly less than n.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public byte[] read(int n) throws IOException;


    /**
    Write a number of bytes to the file.
    @param bs The byte to write.
    @exception IOException Thrown if the underlying system call returns an error code. The message
    is expected to be a mnemonic from errno.h.
    */
    public void write(byte[] b) throws IOException;
}
