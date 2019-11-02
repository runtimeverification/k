// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import jline.internal.Nullable;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;
import org.nustaq.serialization.FSTObjectInput;
import org.nustaq.serialization.FSTObjectOutput;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectStreamException;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.nio.channels.OverlappingFileLockException;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

@RequestScoped
public class BinaryLoader {

    static {
        disableAccessWarnings();
    }

    /**
     * Disables JVM warnings "WARNING: An illegal reflective access operation has occurred" produced by FST.
     * <p>
     * source: https://stackoverflow.com/a/53517025/4182868
     */
    @SuppressWarnings("unchecked")
    public static void disableAccessWarnings() {
        try {
            Class unsafeClass = Class.forName("sun.misc.Unsafe");
            Field field = unsafeClass.getDeclaredField("theUnsafe");
            field.setAccessible(true);
            Object unsafe = field.get(null);

            Method putObjectVolatile =
                    unsafeClass.getDeclaredMethod("putObjectVolatile", Object.class, long.class, Object.class);
            Method staticFieldOffset = unsafeClass.getDeclaredMethod("staticFieldOffset", Field.class);

            Class loggerClass = Class.forName("jdk.internal.module.IllegalAccessLogger");
            Field loggerField = loggerClass.getDeclaredField("logger");
            Long offset = (Long) staticFieldOffset.invoke(unsafe, loggerField);
            putObjectVolatile.invoke(unsafe, loggerClass, offset, null);
            // DISABLE EXCEPTION CHECKSTYLE
        } catch (Exception ignored) {
            // ENABLE EXCEPTION CHECKSTYLE
            //Exception here caused by reflexion will just re-enable the warning.
        }
    }

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
            FileOutputStream out = new FileOutputStream(file); //todo not closing here, for debug. Should be closed in saveSynchronized()
            saveSynchronized(out, o);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + file.getAbsolutePath(), e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to write " + file, e);
        }
    }

    public <T> T loadOrDie(Class<T> cls, File file) {
        try (FileInputStream in = new FileInputStream(file)) {
            return cls.cast(loadSynchronized(in));
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
        try (FileInputStream in = new FileInputStream(file)) {
            return cls.cast(loadSynchronized(in));
        } catch (FileNotFoundException e) {
            //ignored
        } catch (IOException | ClassNotFoundException e) {
            kem.registerInternalHiddenWarning("Invalidating serialized cache due to corruption.", e);
        } catch (InterruptedException e) {
            throw KEMException.criticalError("Interrupted while locking to read " + file.getAbsolutePath(), e);
        }
        return null;
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
            try (FSTObjectOutput serializer = new FSTObjectOutput(out)) { //already buffered
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
            try (FSTObjectInput deserializer = new FSTObjectInput(in)) { //already buffered
                Object obj = deserializer.readObject();
                return obj;
            }
        } finally {
            lock.readLock().unlock();
        }
    }
}
