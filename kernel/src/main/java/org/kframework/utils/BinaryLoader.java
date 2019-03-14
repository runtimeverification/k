// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.nio.channels.FileLock;

@RequestScoped
public class BinaryLoader {

    private final KExceptionManager kem;

    @Inject
    public BinaryLoader(KExceptionManager kem) {
        this.kem = kem;
    }

    public void saveWithLock(File fileName, Object o) throws IOException {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KEMException.criticalError("Could not create directory " + dir);
        }
        try (FileOutputStream out = new FileOutputStream(fileName)) {
            saveWithLock(out, o);
        }
    }

    public void saveOrDie(File fileName, Object o) {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KEMException.criticalError("Could not create directory " + dir);
        }
        try (FileOutputStream out = new FileOutputStream(fileName)) {
            saveWithLock(out, o);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + fileName.getAbsolutePath(), e);
        }
    }

    /**
     * Locks the file before writing, so that it cannot be read by another instance of K. If the file is currently in
     * use, this method will block until lock can be acquired.
     */
    public void saveWithLock(FileOutputStream out, Object o) throws IOException {
        out.getChannel().lock(); //Lock is released automatically when serializer is closed.
        try (ObjectOutputStream serializer = new ObjectOutputStream(new BufferedOutputStream(out))) {
            serializer.writeObject(o);
        }
    }

    public <T> T load(Class<T> cls, File fileName) throws IOException, ClassNotFoundException {
        return cls.cast(load(fileName));
    }

    public <T> T load(Class<T> cls, InputStream in) throws IOException, ClassNotFoundException {
        return cls.cast(load(in));
    }

    public <T> T loadOrDie(Class<T> cls, File fileName) {
        try (InputStream in = new BufferedInputStream(new FileInputStream(fileName))) {
            return loadOrDie(cls, in, fileName.getAbsolutePath());
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + fileName, e);
        }
    }

    public Object load(InputStream in) throws IOException, ClassNotFoundException {
        try (ObjectInputStream deserializer
                = new ObjectInputStream(in)) {
            Object obj = deserializer.readObject();
            return obj;
        }
    }

    public Object load(File fileName) throws IOException, ClassNotFoundException {
        try (InputStream in = new BufferedInputStream(new FileInputStream(fileName))) {
            return load(in);
        }
    }

    public <T> T loadOrDie(Class<T> cls, InputStream in, String fileName) {

        try {
            return load(cls, in);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            throw KEMException.criticalError("Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again.", e);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + fileName, e);
        }
    }
}
