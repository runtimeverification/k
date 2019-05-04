// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.nio.channels.OverlappingFileLockException;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

@RequestScoped
public class BinaryLoader {

    private static ReadWriteLock lock = new ReentrantReadWriteLock();

    private final KExceptionManager kem;

    @Inject
    public BinaryLoader(KExceptionManager kem) {
        this.kem = kem;
    }

    public void saveOrDie(File fileName, Object o) {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KEMException.criticalError("Could not create directory " + dir);
        }
        try (FileOutputStream out = new FileOutputStream(fileName)) {
            saveSynchronized(out, o);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + fileName.getAbsolutePath(), e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to write " + fileName, e);
        }
    }

    /**
     * Locks the file before writing, so that it cannot be read by another instance of K. If the file is currently in
     * use, this method will block until lock can be acquired.
     */
    public void saveSynchronized(FileOutputStream out, Object o) throws IOException, InterruptedException {
        //To protect from concurrent access from another thread
        lock.writeLock().lockInterruptibly();
        try {
            //To protect from concurrent access to same file from another process
            out.getChannel().lock(); //Lock is released automatically when serializer is closed.
            try (ObjectOutputStream serializer = new ObjectOutputStream(out)) { //already buffered
                serializer.writeObject(o);
            }
        } finally {
            lock.writeLock().unlock();
        }
    }

    public Object loadSynchronized(FileInputStream in)
            throws IOException, ClassNotFoundException, InterruptedException {
        //To protect from concurrent access from another thread
        lock.readLock().lockInterruptibly();
        try {
            //To protect from concurrent access to same file from another process
            //Lock is released automatically when serializer is closed.
            try {
                in.getChannel().lock(0L, Long.MAX_VALUE, true);
            } catch (OverlappingFileLockException e) {
                //We are in Nailgun mode. File lock is not needed.
            }
            try (ObjectInputStream deserializer = new ObjectInputStream(in)) { //already buffered
                Object obj = deserializer.readObject();
                return obj;
            }
        } finally {
            lock.readLock().unlock();
        }
    }

    public <T> T load(Class<T> cls, File fileName) throws IOException, ClassNotFoundException {
        try {
            return cls.cast(load(fileName));
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to read " + fileName, e);
        }
    }

    public <T> T load(Class<T> cls, FileInputStream in)
            throws IOException, ClassNotFoundException, InterruptedException {
        return cls.cast(loadSynchronized(in));
    }

    public <T> T loadOrDie(Class<T> cls, File fileName) {
        try (FileInputStream in = new FileInputStream(fileName)) {
            return loadOrDie(cls, in, fileName.getAbsolutePath());
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + fileName, e);
        }
    }

    public Object load(File fileName) throws IOException, ClassNotFoundException, InterruptedException {
        try (FileInputStream in = new FileInputStream(fileName)) {
            return loadSynchronized(in);
        }
    }

    public <T> T loadOrDie(Class<T> cls, FileInputStream in, String fileName) {
        try {
            return load(cls, in);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            throw KEMException.criticalError("Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again.", e);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + fileName, e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to read " + fileName, e);
        }
    }
}
