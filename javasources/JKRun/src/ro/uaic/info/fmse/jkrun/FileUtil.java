package ro.uaic.info.fmse.jkrun;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import org.apache.commons.io.FileUtils;

public class FileUtil {

	public static File createFile(String file) {
		try {
			File file1 = new File(file);
			File f2 = new File(file1.getParent());
			f2.mkdirs();
			return file1;
		} catch (Exception e) {
			Error.report("Error while creating maude file " + file);
		}
		return null;
	}

	public static File createFile(String file, String content) {
		try {
			File file1 = new File(file);
			File f2 = new File(file1.getParent());
			f2.mkdirs();
			BufferedWriter out = new BufferedWriter(new FileWriter(file1));
			if (content != null) {
				out.write(content);
				out.flush();
				out.close();
			}
			return file1;
		} catch (Exception e) {
			Error.report("Error while creating maude file " + file);
		}
		return null;
	}

	public static String generateUniqueFileName(String fileName) {

		int dot = fileName.lastIndexOf(".");
		String name = fileName.substring(0, dot);
		String extension = fileName.substring(dot, fileName.length());

		try {
			return File.createTempFile(name, extension).getName();
		} catch (IOException e) {
			Error.report("Error while generating unique file name:" + e.getMessage());
		}
		return null;
	}
	
	public static String generateUniqueFolderName(String dirName) {
		try {
			return File.createTempFile(dirName, "").getName();
		} catch (IOException e) {
			Error.report("Error while generating unique directory name:" + e.getMessage());
		}
		return null;
	}

	public static String getFileContent(String file) {
		BufferedReader reader;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = null;
			StringBuilder stringBuilder = new StringBuilder();
			while ((line = reader.readLine()) != null) {
				stringBuilder.append(line);
				stringBuilder.append(K.lineSeparator);
			}
			return stringBuilder.toString();
		} catch (FileNotFoundException e) {
			Error.report("Cannot retrieve file content. Make sure that file " + file + " exists.");
		} catch (IOException e) {
			Error.silentReport("Cannot retrieve file content. An IO error occured.");
		}
		return "";
	}

	public static void deleteFile(String fileName) {

		File f = new File(fileName);

		// Make sure the file or directory exists
		if (!f.exists())
			throw new IllegalArgumentException("Delete: no such file or directory:" + fileName);

		// Attempt to delete it
		boolean success = f.delete();

		if (!success)
			throw new IllegalArgumentException("Delete: deletion failed");
	}

	public static boolean deleteDirectory(File path) {
		if (path.exists()) {
			File[] files = path.listFiles();
			for (int i = 0; i < files.length; i++) {
				if (files[i].isDirectory()) {
					deleteDirectory(files[i]);
				} else {
					files[i].delete();
				}
			}
		}
		return (path.delete());
	}
	
	public static void renameFolder(String oldName, String newName) throws IOException {
		File srcFile = new File(oldName);
		boolean bSucceeded = false;
		try {
			File destFile = new File(newName);
			//test if the krun directory is empty and if is not empty delete it
			if (destFile.exists()) {
				if (!FileUtil.deleteDirectory(destFile)) {
					throw new IOException(oldName + " was not successfully deleted");
				}
			}
			//rename krun temp directory into "krun" 
			if (!srcFile.renameTo(destFile)) {
				throw new IOException(oldName + " was not successfully renamed to " + newName);
			} else {
				bSucceeded = true;
			}
		} finally {
			if (bSucceeded) {
				srcFile.delete();
			}
		}
	}

	public static String parseResultOutputMaude(String file) {
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = null;
			boolean found = false;
			StringBuilder stringBuilder = new StringBuilder();
			
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("Maude> Bye.")) {
					break;
				}
				if (found) {
					line = reader.readLine(); 
                    found = false;
				}
				if (line.startsWith("Maude> rewrites:")) {
					found = true;
				}
				else {
					stringBuilder.append(line);
				}
			}

			return stringBuilder.toString();

		} catch (FileNotFoundException e) {
			Error.report("Cannot retrieve file content. Make sure that file " + file + " exists.");
		} catch (IOException e) {
			Error.silentReport("Cannot retrieve file content. An IO error occured.");
		} finally {
			try {
				reader.close();
			} catch (IOException e) {
				//e.printStackTrace();
				Error.report("Error while parsing result output maude:" + e.getMessage());
			}
		}
		return null;
	}
	
	public static List<String> parseSearchOutputMaude(String file) {
		BufferedReader reader = null;
		List<String> l = new ArrayList<String>();
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = null;
			boolean found = false;
			StringBuilder stringBuilder = new StringBuilder();
			
			while ((line = reader.readLine()) != null) {
				if (line.length() == 0) {
					l.add(stringBuilder.toString());
					stringBuilder = new StringBuilder();
				}
				if (line.startsWith("No more solutions.")) {
					break;
				}
				if (found) {
					//jump two lines
					for (int j = 0; j < 2; j++) {
					    line = reader.readLine(); 
					}
                    found = false;
				}
				//it will match a string like: "Solution 1248465 (state 45)"
				if (line.matches("Solution\\s\\d+\\s\\(state\\s\\d+\\)")) {
					found = true;
				}
				else if (! line.startsWith("Maude>")) {
					stringBuilder.append(line);
				}
			}
			return l;

		} catch (FileNotFoundException e) {
			Error.report("Cannot retrieve file content. Make sure that file " + file + " exists.");
		} catch (IOException e) {
			Error.silentReport("Cannot retrieve file content. An IO error occured.");
		} finally {
			try {
				reader.close();
			} catch (IOException e) {
				Error.report("Error while parsing search output maude:" + e.getMessage());
			}
		}
		return null;
	}

	public static ArrayList<File> searchFiles(String path, String extension, boolean recursive) {
		ArrayList<File> result = new ArrayList<File>();
		File dir = new File(path);

		if (dir.isFile()) {
			Error.report("The path given as argument (" + path + ") is a file and not a directory.");
		} else if (dir.isDirectory()) {
			try {
				String[] extensions = { extension };
				Collection<?> files = FileUtils.listFiles(dir, extensions, recursive);
				for (Iterator<?> iterator = files.iterator(); iterator.hasNext();) {
					File file = (File) iterator.next();
					result.add(file);
				}
			} catch (Exception e) {
				Error.report("Error while searching files:" + e.getMessage());
			}
		}
		return result;
	}

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

	public static String getFilename(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		int sep = fullPath.lastIndexOf(pathSeparator);
		return fullPath.substring(sep + 1, dot);
	}

	public static String getExternalParserName(String fullPath, String pathSeparator) {
		int sep = fullPath.lastIndexOf(pathSeparator);
		return fullPath.substring(sep + 1);
	}

	public static String dropExtension(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		return fullPath.substring(0, dot);
	}

	public static String dropKExtension(String fullPath, String extensionSeparator, String pathSeparator) {
		if ("k".equals(getExtension(fullPath, ".", pathSeparator))) {
			return dropExtension(fullPath, extensionSeparator, pathSeparator);
		} else {
			return fullPath;
		}
	}
	
	/*
	 * count the number of underscores from the String op
	 */
	public static int countUnderscores(String op) {
		int count = 0;
	    int index = 0;
	    StringBuilder sb = new StringBuilder(op);
		while (index != -1) {
			index = sb.indexOf("_", index);
			if (index != -1) {
				count++;
				index++;
			}
		}
		return count;
	}
	
}
