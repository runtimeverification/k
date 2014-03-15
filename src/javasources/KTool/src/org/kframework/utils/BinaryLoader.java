package org.kframework.utils;

import java.io.*;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

public class BinaryLoader {

    public static void save(String fileName, Object o) {
        try(ObjectOutputStream serializer
                = new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(fileName)))) {
            serializer.writeObject(o);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }
    
    public static <T> T load(Class<T> cls, String fileName) {
        return cls.cast(load(fileName));
    }

    public static Object load(String fileName) {
        try (ObjectInputStream deserializer
                 = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)))) {
            return deserializer.readObject();
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
            System.exit(1);
        } catch (IOException e) {
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, "Kompiled definition is out of date with latest version of the K tool. Please re-run kompile and try again."));
        }
        return null;
    }    
}
