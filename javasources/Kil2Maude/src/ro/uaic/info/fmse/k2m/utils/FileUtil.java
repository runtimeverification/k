package ro.uaic.info.fmse.k2m.utils;

import java.io.BufferedInputStream;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;

public class FileUtil {
	public static String readFileAsString(String filePath) {
		byte[] buffer = new byte[(int) new File(filePath).length()];
		BufferedInputStream f = null;
		try {
			f = new BufferedInputStream(new FileInputStream(filePath));
			f.read(buffer);
		} catch (Exception e) {
			System.out.println(e.getLocalizedMessage());
		} finally {
			if (f != null)
				try {
					f.close();
				} catch (IOException ignored) {
				}
		}
		return new String(buffer);
	}

	public static void saveInFile(String file, String content) {
		try {
			File file1 = new File(file);
			// File f2 = new File(file1.getParent());
			// f2.mkdirs();
			// file1.createNewFile();

			BufferedWriter out = new BufferedWriter(new FileWriter(file1));
			if (content != null) {
				out.write(content);
				out.flush();
				out.close();
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
