package org.kframework.krun;

import java.io.*;

public class FileUtil {

	// create a file with the specified name, create parent directory if it doesn't exist
	public static File createFile(String file) {
		try {
			File file1 = new File(file);
			File f2 = new File(file1.getParent());
			f2.mkdirs();
			return file1;
		} catch (Exception e) {
			Error.report("Error while creating file " + file);
		}
		return null;
	}

	// generate an unique name for a folder with the name dirName
	public static String generateUniqueFolderName(String dirName) {
		try {
			return File.createTempFile(dirName, "").getName();
		} catch (IOException e) {
			Error.report("Error while generating unique directory name:" + e.getMessage());
		}
		return null;
	}

    //parse the output of Maude when --output-mode=raw
	//get the extension of a file specified by the fullPath with the specified extension and path separator
	public static String getExtension(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot, pos;
		String aux;

		pos = fullPath.lastIndexOf(pathSeparator);
		aux = fullPath.substring(pos + 1);
		if (aux.indexOf(extensionSeparator) == -1) {
			return "";
		} else {
			dot = aux.lastIndexOf(extensionSeparator);
			return aux.substring(dot + 1);
		}
	}
}
