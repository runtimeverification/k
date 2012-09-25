package org.kframework.utils.utils.file;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class FileUtil {

	public static void saveInFile(String file, String content) {
		try {
			File file1 = new File(file);
			File f2 = new File(file1.getParent());
			f2.mkdirs();
			// file1.createNewFile();

			BufferedWriter out = new BufferedWriter(new FileWriter(file1));
			if (content != null) {
				out.write(content);
				out.flush();
				out.close();
			}
		} catch (IOException e) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot save file content: " + file, "internal", "FileUtil.java"));
		}
	}

	public static String getExtension(String file) {
		int idx = file.lastIndexOf(".");
		if (idx < 0)
			return null;
		return file.substring(idx);
	}

	public static String stripExtension(String file) {
		int idx = file.lastIndexOf(".");
		if (idx < 0)
			return file;
		return file.substring(0, idx);
	}

	/**
	 * Get language name in uppercase (main module name) given the filename of definition.
	 */
	public static String getMainModule(String filename) {
		return stripExtension(filename).toUpperCase();
	}

	public static String getFileContent(String file) {
		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = null;
			StringBuilder stringBuilder = new StringBuilder();
			String ls = System.getProperty("line.separator");
			while ((line = reader.readLine()) != null) {
				stringBuilder.append(line);
				stringBuilder.append(ls);
			}
			return stringBuilder.toString();

		} catch (FileNotFoundException e) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot retrieve file content. Make sure that file: " + file + " exists.", "internal", "FileUtil.java"));
		} catch (IOException e) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot retrieve file content. An IO error occured: " + file, "internal", "FileUtil.java"));
		}

		return "";
	}

	public static void delete(String file) {
		new File(file).delete();
	}
}
