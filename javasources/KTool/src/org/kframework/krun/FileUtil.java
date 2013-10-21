package org.kframework.krun;

import org.apache.commons.io.FileUtils;

import java.io.*;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

public class FileUtil {

	//create a file with the specified name and place it under a subfolder
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

	//create a file with the specified name and content and place it under a subfolder
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

	//generate an unique name for a file with the name fileName
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
	
	//generate an unique name for a folder with the name dirName
	public static String generateUniqueFolderName(String dirName) {
		try {
			return File.createTempFile(dirName, "").getName();
		} catch (IOException e) {
			Error.report("Error while generating unique directory name:" + e.getMessage());
		}
		return null;
	}

	//return the content of a file 
	public static String getFileContent(String file) {
		BufferedReader reader = null;
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
		finally{
			if (reader != null) {
				try {
					reader.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		return "";
	}

	//delete a file specified by the fileName
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

	public static void deleteDirectory(File dir) throws IOException {
        deleteDirectory(dir.toPath());
	}

    private static void deleteDirectory(Path path) throws IOException {
        if (Files.exists(path)) {
            if (Files.isDirectory(path)) {
                for (Path file : Files.newDirectoryStream(path)) {
                    deleteDirectory(file);
                }
            }
            Files.delete(path);
        }
    }

    //rename a folder having it's current name oldName with the specified newName
	public static void renameFolder(String oldName, String newName) throws IOException {
		Path srcFile = Paths.get(oldName);
		
		if (Files.exists(srcFile)) {
			RandomAccessFile lockFile = new RandomAccessFile(new File(K.kdir + K.fileSeparator + "krun.lock"),"rw");
			FileChannel channel = lockFile.getChannel();
			FileLock lock = channel.lock();

            Path destFile = Paths.get(newName);
            //test if the krun directory is empty and if is not empty delete it
            FileUtil.deleteDirectory(destFile);
            //rename krun temp directory into "krun"
            Files.move(srcFile, destFile);

			lock.release();
			lockFile.close();
		}
	}

	//parse the output of Maude when --output-mode=raw
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
					//jump one line
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
	
	//parse the output of Maude when --output-mode=raw and --ltlmc options are provided
	public static String parseModelCheckingOutputMaude(String file) {
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new FileReader(file));
			String line = null;
			boolean before = true;
			StringBuilder stringBuilder = new StringBuilder();
			
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("Maude> Bye.")) {
					break;
				}
				if (before) {
					//jump three lines
					for (int j = 0; j < 3; j++) {
						line = reader.readLine();
					}
					before = false;
				}
				if (line.startsWith("result KItem: ")) {
					String pattern = new String("result KItem: ");
					int index = line.indexOf(pattern);
					String s = line.substring(index + pattern.length());
					stringBuilder.append(s);
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
	
	//parse the output of Maude when --output-mode=raw and search command is used 
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

	//search for files in the given path, with the specified extension and recursively if recursive=true 
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
	
	//search for subfolders in the given path, having a name that matches the pattern
	public static File[] searchSubFolders (String path, final String pattern) {
		// This filter only returns directories with a name that matches the pattern
		FileFilter fileFilter = new FileFilter() {
		    public boolean accept(File file) {
		        return (file.isDirectory() && file.getName().matches(pattern));
		    }
		};
		File dir = new File(path);
		File[] files = dir.listFiles(fileFilter);
		return files;
	}

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
    
	//for folder/subfolder/fileName.extension it will return fileName (where e.g. "." - extensionSeparator and "/" - pathSeparator)
	public static String getFilename(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		int sep = fullPath.lastIndexOf(pathSeparator);
		return fullPath.substring(sep + 1, dot);
	}

	//for folder/subfolder/fileName.extension it will return folder/subfolder/fileName
	public static String dropExtension(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		return fullPath.substring(0, dot);
	}

	//drop the .k extension from the name of a file
	public static String dropKExtension(String fullPath, String extensionSeparator, String pathSeparator) {
		if ("k".equals(getExtension(fullPath, ".", pathSeparator))) {
			return dropExtension(fullPath, extensionSeparator, pathSeparator);
		} else {
			return fullPath;
		}
	}
	
}
