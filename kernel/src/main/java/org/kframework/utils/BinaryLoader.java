// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import jline.internal.Nullable;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.channels.OverlappingFileLockException;
import java.util.Collections;
import java.util.HashMap;
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

    public void saveOrDie(File file, Object o) {
        File dir = file.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KEMException.criticalError("Could not create directory " + dir);
        }
        try {
            saveSynchronized(file, o);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + file.getAbsolutePath(), e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to write " + file, e);
        }
    }

    public <T> T loadOrDie(Class<T> cls, File file) {
        try {
            return loadSynchronized(file, cls);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            throw KEMException.criticalError("Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again.", e);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + file.getAbsolutePath(), e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to read " + file.getAbsolutePath(), e);
        }
    }

    @Nullable
    public <T> T loadCache(Class<T> cls, File file) {
        try {
            return loadSynchronized(file, cls);
        } catch (FileNotFoundException e) {
            //ignored
        } catch (IOException | ClassNotFoundException e) {
            kem.registerInternalWarning(ExceptionType.INVALIDATED_CACHE, "Invalidating serialized cache due to corruption.", e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to read " + file.getAbsolutePath(), e);
        }
        return null;
    }

    /**
     * Locks the file before writing, so that it cannot be read by another instance of K. If the file is currently in
     * use, this method will block until lock can be acquired.
     */
    private void saveSynchronized(File file, Object o) throws IOException, InterruptedException {
        //To protect from concurrent access from another thread, in kserver mode
        lock.writeLock().lockInterruptibly();
        //JDK API limitation: there's no API to atomically open a file for writing and lock it.
        //Consequently, if another process reads a file between the moments this thread opens a stream and acquires a
        // lock, it will see an empty file.
        // To prevent this we acquire file lock before opening the stream, using another stream.
        try (FileOutputStream lockStream = new FileOutputStream(file, true)) {
            //To protect from concurrent access to same file from another process, in standalone mode
            lockStream.getChannel().lock(); //Lock is released automatically when lockStream is closed.
            //already buffered
            try (ObjectOutputStream serializer = new ObjectOutputStream(new FileOutputStream(file))) {
                serializer.writeObject(o);
            }
        } finally {
            lock.writeLock().unlock();
        }
    }

    private <T> T loadSynchronized(File file, Class<T> cls) throws IOException, ClassNotFoundException, InterruptedException {
        //To protect from concurrent access from another thread
        lock.readLock().lockInterruptibly();
        //There's no issue if input stream is opened before lock is acquired
        try (FileInputStream in = new FileInputStream(file)) {
            //To protect from concurrent access to same file from another process
            //Lock is released automatically when stream is closed.
            try {
                in.getChannel().lock(0L, Long.MAX_VALUE, true);
            } catch (OverlappingFileLockException e) {
                //We are in Nailgun mode. File lock is not needed.
            }
            try (ObjectInputStream deserializer = new ObjectInputStream(in)) { //already buffered
                Object obj = deserializer.readObject();
                return cls.cast(obj);
            }
        } finally {
            lock.readLock().unlock();
        }
    }
}
