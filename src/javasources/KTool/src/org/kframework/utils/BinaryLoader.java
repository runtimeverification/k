package org.kframework.utils;

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.OutputStream;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

public class BinaryLoader {

	public static void toBinary(Object o, OutputStream out) {
		try {
			ObjectOutputStream serializer = new ObjectOutputStream(out);
			serializer.writeObject(o);
			serializer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static Object fromBinary(InputStream in) {
		try {
			ObjectInputStream deserializer = new ObjectInputStream(in);
			Object o = deserializer.readObject();
			deserializer.close();
			return o;
		} catch (IOException e) {
			GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, "Kompiled definition is out of date with latest version of the K tool. Please re-run kompile and try again."));
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
		return null;
	}	
}
