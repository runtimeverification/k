// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import org.kframework.kore.K;
import org.kframework.parser.binary.BinaryParser;
import org.kframework.unparser.ToBinary;
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
import java.io.OutputStream;

@RequestScoped
public class BinaryLoader {

    private final KExceptionManager kem;

    @Inject
    public BinaryLoader(
            KExceptionManager kem) {
        this.kem = kem;
    }

    public void save(File fileName, Object o) throws IOException {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KEMException.criticalError("Could not create directory " + dir);
        }
        try (OutputStream out = new FileOutputStream(fileName)) {
            save(out, o);
        }
    }

    public void saveOrDie(File fileName, Object o) {
        File dir = fileName.getAbsoluteFile().getParentFile();
        if (!dir.exists() && !dir.mkdirs()) {
            throw KEMException.criticalError("Could not create directory " + dir);
        }
        try (OutputStream out = new FileOutputStream(fileName)) {
            saveOrDie(out, o, fileName.getAbsolutePath());
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + fileName, e);
        }
    }

    private void saveOrDie(OutputStream out, Object o, String fileName) {
        try {
            save(out, o);
        } catch (IOException e) {
            throw KEMException.criticalError("Could not write to " + fileName, e);
        }
    }

    public void saveOrDie(OutputStream out, Object o) {
        saveOrDie(out, o, "output stream");
    }

    public void save(OutputStream out, Object o) throws IOException {
        if (o instanceof K) {
            ToBinary.apply(out, (K)o);
        } else {
            try (ObjectOutputStream serializer
                         = new ObjectOutputStream(new BufferedOutputStream(out))) {
                serializer.writeObject(o);
            }
        }
    }

    public <T> T load(Class<T> cls, File fileName) throws IOException, ClassNotFoundException {
        return cls.cast(load(fileName, K.class.isAssignableFrom(cls)));
    }

    public <T> T load(Class<T> cls, InputStream in) throws IOException, ClassNotFoundException {
        return cls.cast(load(in, K.class.isAssignableFrom(cls)));
    }

    public <T> T loadOrDie(Class<T> cls, File fileName) {
        try (InputStream in = new BufferedInputStream(new FileInputStream(fileName))) {
            return loadOrDie(cls, in, fileName.getAbsolutePath());
        } catch (IOException e) {
            throw KEMException.criticalError("Could not read from " + fileName, e);
        }
    }

    private Object load(InputStream in, boolean isK) throws IOException, ClassNotFoundException {
        if (isK) {
            return BinaryParser.parse(in);
        } else {
            try (ObjectInputStream deserializer
                         = new ObjectInputStream(in)) {
                Object obj = deserializer.readObject();
                return obj;
            }
        }
    }

    private Object load(File fileName, boolean isK) throws IOException, ClassNotFoundException {
        try (InputStream in = new BufferedInputStream(new FileInputStream(fileName))) {
            return load(in, isK);
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
