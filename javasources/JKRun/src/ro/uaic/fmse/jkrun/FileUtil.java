package ro.uaic.fmse.jkrun;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

import org.apache.commons.io.FileUtils;

public class FileUtil {

	// save content in file
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
			Error.report("Internal error: Cannot save file content.");
		}
	}

	public static void createFile(String file, String content) {
		try {
			File file1 = new File(file);
			file1.setExecutable(true);
			BufferedWriter out = new BufferedWriter(new FileWriter(file1));
			if (content != null) {
				out.write(content);
				out.flush();
				out.close();
			}
		} catch (IOException e) {
			Error.report("Internal error: Cannot save file content.");
		}
	}

	public static File createMaudeFile(String file) {
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

		// Make sure the file or directory exists and isn't write protected
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

	// appends the content from the srFile to dtFile
	public static void copyfile(String srFile, String dtFile) {

		try {
			File f1 = new File(srFile);
			File f2 = new File(dtFile);
			InputStream in = new FileInputStream(f1);

			// For Append the file.
			OutputStream out = new FileOutputStream(f2, true);

			// For Overwrite the file.
			// OutputStream out = new FileOutputStream(f2);
			byte[] buf = new byte[1024];
			int len;
			while ((len = in.read(buf)) > 0) {
				out.write(buf, 0, len);
			}
			in.close();
			out.close();
		} catch (FileNotFoundException ex) {
			Error.report(ex.getMessage() + " in the specified directory.");
		} catch (IOException e) {
			System.out.println(e.getMessage());
		}
	}

	// creates a new file named fileName in which copies the content from
	// srcFile and at the end appends the string s
	public static void copyFile(String fileName, String srcFile, String s) {

		try {
			File destFile = new File(fileName);
			File inFile = new File(srcFile);

			InputStream in = new FileInputStream(inFile);
			OutputStream out = new FileOutputStream(destFile);

			byte[] buf = new byte[1024];
			int len;
			while ((len = in.read(buf)) > 0) {
				out.write(buf, 0, len);
			}
			byte[] b = s.getBytes();
			out.write(b);
			in.close();
			out.close();
		} catch (FileNotFoundException ex) {
			Error.report(ex.getMessage() + " in the specified directory.");
		} catch (IOException e) {
			System.out.println(e.getMessage());
		}

	}

	public static String parseOutputMaude(String file) {
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = null;
			int startLine = 0, i = 0;
			boolean ok = true;
			StringBuilder stringBuilder = new StringBuilder("\n");
			while ((line = reader.readLine()) != null) {
				if (line.endsWith("</ T >")) {
					ok = false;
					stringBuilder.append(line);
				}
				if (!ok) {
					break;
				}
				if (startLine != 0) {
					stringBuilder.append(line);
					stringBuilder.append(K.lineSeparator);
				}
				if (line.startsWith("< T >")) {
					startLine = i;
					stringBuilder.append(line);
				}
				i++;
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
				e.printStackTrace();
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
				e.printStackTrace();
			}
		}
		return result;
	}

	public static String getExtension(String fullPath, String extensionSeparator) {
		int dot;
		if (fullPath.indexOf(extensionSeparator) == -1) {
			return "";
		} else {
			dot = fullPath.lastIndexOf(extensionSeparator);
			return fullPath.substring(dot + 1);
		}
	}

	public static String getFilename(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		int sep = fullPath.lastIndexOf(pathSeparator);
		return fullPath.substring(sep + 1, dot);
	}
	
	public static String dropExtension(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		return fullPath.substring(0, dot);
	}
	
	public static String dropKExtension(String fullPath, String extensionSeparator, String pathSeparator) {
        if (getExtension(fullPath, ".").equals("k")) {
                return dropExtension(fullPath, extensionSeparator, pathSeparator);
        }
        else {
                return fullPath;
        }
}


}
