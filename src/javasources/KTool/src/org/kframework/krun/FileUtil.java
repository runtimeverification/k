package org.kframework.krun;

import java.io.*;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.file.*;

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

	public static void deleteDirectory(File dir) throws IOException {
        deleteDirectory(dir.toPath());
	}

    private static void deleteDirectory(Path path) throws IOException {
        if (Files.exists(path)) {
            if (Files.isDirectory(path)) {
                DirectoryStream<Path> paths = Files.newDirectoryStream(path);
                for (Path file : paths) {
                    deleteDirectory(file);
                }
                paths.close();
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

            try {
                Path destFile = Paths.get(newName);

                //test if the krun directory exists and if true delete it
                deleteDirectory(destFile);

                //rename krun temp directory into "krun"
                try {
                    Files.move(srcFile, destFile);
                    //Should never happen, but in case it does
                    // the code below will fail and hopefully will provide more debug information.
                } catch (AccessDeniedException e) {
                    copyDir(srcFile, destFile);
                    deleteDirectory(srcFile);
                }
            } finally {
                lock.release();
                lockFile.close();
            }
		}
	}

    private static void copyDir(Path srcFile, Path destFile) throws IOException {
        if (Files.isRegularFile(srcFile)) {
            Files.copy(srcFile, destFile);
        } else {
            Files.createDirectory(destFile);
            DirectoryStream<Path> paths = Files.newDirectoryStream(srcFile);
            for( Path path : paths) {
                copyDir(path, Paths.get(destFile.toString(), path.getFileName().toString()));
            }
            paths.close();
        }
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
    
	//for folder/subfolder/fileName.extension it will return fileName (where e.g. "." - extensionSeparator and "/" - pathSeparator)
	public static String getFilename(String fullPath, String extensionSeparator, String pathSeparator) {
		int dot = fullPath.lastIndexOf(extensionSeparator);
		int sep = fullPath.lastIndexOf(pathSeparator);
		return fullPath.substring(sep + 1, dot);
	}
}
