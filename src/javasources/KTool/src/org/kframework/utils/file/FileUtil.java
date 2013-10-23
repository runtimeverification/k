package org.kframework.utils.file;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.util.List;

import static org.apache.commons.io.FileUtils.copyFile;
import static org.apache.commons.io.FileUtils.readFileToString;
import static org.apache.commons.io.FileUtils.writeStringToFile;

public class FileUtil {

	public static void saveInFile(String file, String content) {
		try {
            writeStringToFile(new File(file), content);
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
		try {
            return readFileToString(new File(file));
		} catch (FileNotFoundException e) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot retrieve file content. Make sure that file: " + file + " exists.", "internal", "FileUtil.java"));
		} catch (IOException e) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot retrieve file content. An IO error occured: " + file, "internal", "FileUtil.java"));
		}
		return "";
	}

	public static void copyFiles(List<File> files, File parentFile) {
		for (File file : files) {
			try {
				copyFile(new File(file.getCanonicalPath()), new File(parentFile.getCanonicalPath() + File.separator + file.getName()));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
}
