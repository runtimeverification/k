// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.*;

import org.kframework.utils.errorsystem.KExceptionManager;

import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Singleton;

@Singleton
public class BinaryLoader {

    private final KExceptionManager kem;
    // Do *NOT* use this for anything except its intended usage!
    // We are injecting the injector because of limitations of java deserialization *ONLY*.
    // Eventually once the framework is completely converted this will go away and
    // be replaced by serialized objects containing data only.
    private final Injector injector;

    @Inject
    public BinaryLoader(
            KExceptionManager kem,
            Injector injector) {
        this.kem = kem;
        this.injector = injector;
    }

    public void save(File fileName, Object o) throws IOException {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KExceptionManager.criticalError("Could not create directory " + dir);
        }
        try (OutputStream out = new FileOutputStream(fileName)) {
            save(out, o);
        }
    }

    public void saveOrDie(File fileName, Object o) {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KExceptionManager.criticalError("Could not create directory " + dir);
        }
        try (OutputStream out = new FileOutputStream(fileName)) {
            saveOrDie(out, o, fileName.getAbsolutePath());
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not write to " + fileName, e);
        }
    }

    private void saveOrDie(OutputStream out, Object o, String fileName) {
        try {
            save(out, o);
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not write to " + fileName, e);
        }
    }

    public void saveOrDie(OutputStream out, Object o) {
        saveOrDie(out, o, "output stream");
    }

    public void save(OutputStream out, Object o) throws IOException {
        try(ObjectOutputStream serializer
                = new ObjectOutputStream(new BufferedOutputStream(out))) {
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
            throw KExceptionManager.criticalError("Could not read from " + fileName, e);
        }
    }

    public Object load(InputStream in) throws IOException, ClassNotFoundException {
        try (ObjectInputStream deserializer
                = new ObjectInputStream(in)) {
            Object obj = deserializer.readObject();
            injector.injectMembers(obj);
            return obj;
        }
    }

    public Object load(File fileName) throws IOException, ClassNotFoundException {
        try (InputStream in = new BufferedInputStream(new FileInputStream(fileName))) {
            return load(in);
        }
    }

    public <T> T loadOrDie(Class<T> cls, InputStream in) {
        return loadOrDie(cls, in, "input stream");
    }

    private <T> T loadOrDie(Class<T> cls, InputStream in, String fileName) {

        try {
            return load(cls, in);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            throw KExceptionManager.criticalError("Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again.", e);
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not read from " + fileName, e);
        }
    }
}
