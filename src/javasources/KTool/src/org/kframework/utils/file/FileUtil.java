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

    // create a file with the specified name, create parent directory if it doesn't exist
    public static File createFile(String file) {
        try {
            File file1 = new File(file);
            File f2 = new File(file1.getParent());
            f2.mkdirs();
            return file1;
        } catch (Exception e) {
            org.kframework.krun.Error.report("Error while creating file " + file);
        }
        return null;
    }

    // generate an unique name for a folder with the name dirName
    public static String generateUniqueFolderName(String dirName) {
        try {
            return File.createTempFile(dirName, "").getName();
        } catch (IOException e) {
            org.kframework.krun.Error.report("Error while generating unique directory name:" + e.getMessage());
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
        if (!aux.contains(extensionSeparator)) {
            return "";
        } else {
            dot = aux.lastIndexOf(extensionSeparator);
            return aux.substring(dot + 1);
        }
    }
}
