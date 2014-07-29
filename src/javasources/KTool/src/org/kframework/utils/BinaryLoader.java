// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.*;

import org.kframework.utils.general.GlobalSettings;

public class BinaryLoader {

    public static void save(String fileName, Object o) throws IOException {
        save(new FileOutputStream(fileName), o);
    }

    public static void saveOrDie(String fileName, Object o) {
        try {
            saveOrDie(new FileOutputStream(fileName), o, fileName);
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError("Could not write to " + fileName, e);
        }
    }

    private static void saveOrDie(OutputStream out, Object o, String fileName) {
        try {
            save(out, o);
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError("Could not write to " + fileName, e);
        }
    }

    public static void saveOrDie(OutputStream out, Object o) {
        saveOrDie(out, o, "output stream");
    }

    public static void save(OutputStream out, Object o) throws IOException {
        try(ObjectOutputStream serializer
                = new ObjectOutputStream(new BufferedOutputStream(out))) {
            serializer.writeObject(o);
        }
    }

    public static <T> T load(Class<T> cls, String fileName) throws IOException, ClassNotFoundException {
        return cls.cast(load(fileName));
    }

    public static <T> T loadOrDie(Class<T> cls, String fileName) {
        try {
            return load(cls, fileName);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            GlobalSettings.kem.registerCriticalError("Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again.", e);
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError("Could not read from " + fileName, e);
        }
        return null;
    }

    public static Object load(String fileName) throws IOException, ClassNotFoundException {
        try (ObjectInputStream deserializer
                     = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)))) {
            return deserializer.readObject();
        }
    }
}
