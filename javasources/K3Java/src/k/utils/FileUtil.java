package k.utils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;


public class FileUtil {

	public static void saveInFile(String file, String content) {
		try {
			File file1 = new File(file);
			File f2 = new File(file1.getParent());
			f2.mkdirs();
			//file1.createNewFile();

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

	public static String getExtension(String file) {
		int idx = file.lastIndexOf(".");
		if (idx<0) return null;
		return file.substring(idx);
	}	
	
	public static String stripExtension(String file) {
		int idx = file.lastIndexOf(".");
		if (idx<0) return file;
		return file.substring(0,idx);
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
			Error.report("Cannot retrieve file content. Make sure that file "
					+ file + " exists.");
		} catch (IOException e) {
			Error.silentReport("Cannot retrieve file content. An IO error occured.");
		}

		return "";
	}
	
	public static void delete(String file)
	{
		new File(file).delete();
	}

}
