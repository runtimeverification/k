// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.*;

import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class BinaryLoader {

    public static void save(String fileName, Object o) throws IOException {
        save(new FileOutputStream(fileName), o, fileName);
    }
    
    public static void save(String fileName, Object o, Context context) {
        save(fileName, o, context.globalOptions.debug);
    }
    
    public static void save(String fileName, Object o, boolean debug) {
        try {
            save(fileName, o);
        } catch (IOException e) {
            if (debug) {
                e.printStackTrace();
            }
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, 
                    "Could not write to " + fileName));
        }
    }
    
    public static void save(OutputStream out, Object o) throws IOException {
        save(out, o, "output stream");
    }
    
    private static void save(OutputStream out, Object o, String name) throws IOException {
        try(ObjectOutputStream serializer
                = new ObjectOutputStream(new BufferedOutputStream(out))) {
            serializer.writeObject(o);
        }
    }
    
    public static <T> T load(Class<T> cls, String fileName) throws IOException, ClassNotFoundException {
        return cls.cast(load(fileName));
    }
    
    public static <T> T load(Class<T> cls, String fileName, Context context) {
        return load(cls, fileName, context.globalOptions.debug);
    }
    
    public static <T> T load(Class<T> cls, String fileName, boolean debug) {
        try {
            return load(cls, fileName);
        } catch (ClassNotFoundException e) {
            throw new AssertionError("Something wrong with deserialization", e);
        } catch (ObjectStreamException e) {
            if (debug) {
                e.printStackTrace();
            }
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, 
                    KException.KExceptionGroup.CRITICAL, "Kompiled definition is out of date with "
                    + "the latest version of the K tool. Please re-run kompile and try again."));
        } catch (IOException e) {
            if (debug) {
                e.printStackTrace();
            }
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, 
                    "Could not read from " + fileName));
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
