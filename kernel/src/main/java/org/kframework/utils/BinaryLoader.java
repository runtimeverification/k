// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import javax.annotation.Nullable;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.nio.channels.OverlappingFileLockException;
import java.util.Collections;
import java.util.HashMap;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

@RequestScoped
public class BinaryLoader {

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
            saveImpl(file, o);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + file.getAbsolutePath(), e);
        }
    }

    public <T> T loadOrDie(Class<T> cls, File file) {
        try {
            return loadImpl(file, cls);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            throw KEMException.criticalError("Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again.", e);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + file.getAbsolutePath(), e);
        }
    }

    @Nullable
    public <T> T loadCache(Class<T> cls, File file) {
        try {
            return loadImpl(file, cls);
        } catch (FileNotFoundException e) {
            //ignored
        } catch (IOException | ClassNotFoundException e) {
            kem.registerInternalWarning(ExceptionType.INVALIDATED_CACHE, "Invalidating serialized cache due to corruption.", e);
        }
        return null;
    }

    /**
     * Locks the file before writing, so that it cannot be read by another instance of K. If the file is currently in
     * use, this method will block until lock can be acquired.
     */
    private void saveImpl(File file, Object o) throws IOException {
        // we want to atomically update the file in case two kprove threads are writing to the same cache at the same time.
        Path tempFile = Files.createTempFile(file.getCanonicalFile().getParentFile().toPath(), "tmp", ".bin");
        try (ObjectOutputStream serializer = new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(tempFile.toFile())))) {
            serializer.writeObject(o);
        }
        Files.move(tempFile, file.toPath(), StandardCopyOption.ATOMIC_MOVE);
    }

    private <T> T loadImpl(File file, Class<T> cls) throws IOException, ClassNotFoundException {
        try (ObjectInputStream deserializer = new ObjectInputStream(new BufferedInputStream(new FileInputStream(file)))) { //already buffered
            Object obj = deserializer.readObject();
            return cls.cast(obj);
        }
    }
}
