package org.kframework.utils.file;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.nio.channels.FileChannel;
import java.util.List;

public class FileUtil {

	public static void saveInFile(String file, String content) {
		try {
			File file1 = new File(new File(file).getAbsolutePath()); // to avoid null from getParent()
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
		try {
			BufferedReader reader = new BufferedReader(new FileReader(file));
			String line = null;
			StringBuilder stringBuilder = new StringBuilder();
			String ls = System.getProperty("line.separator");
			while ((line = reader.readLine()) != null) {
				stringBuilder.append(line);
				stringBuilder.append(ls);
			}
			reader.close();
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

	public static void copyFiles(List<File> files, File parentFile) {
		for (File file : files) {
			try {
				copyFile(file.getCanonicalPath(), parentFile.getCanonicalPath() + File.separator + file.getName());
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	public static void copyFile(String fromFile, String toFile) throws IOException {
        FileInputStream source = new FileInputStream(fromFile);
        try {
        FileOutputStream destination = new FileOutputStream(toFile);
        try {
 
        FileChannel sourceFileChannel = source.getChannel();
        FileChannel destinationFileChannel = destination.getChannel();
 
        long size = sourceFileChannel.size();
        sourceFileChannel.transferTo(0, size, destinationFileChannel);
        } finally {
        	destination.close();
        }
        } finally {
        	source.close();
        }
	}
}
