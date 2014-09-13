// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.file;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.text.DateFormat;
import java.text.Format;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Properties;
import java.util.UUID;

import static org.apache.commons.io.FileUtils.readFileToString;
import static org.apache.commons.io.FileUtils.writeStringToFile;

public class FileUtil {

    static final Field stringBuilderValue;
    static final Field stringBuilderCount;

    static {
        try {
            final Class<?> abstractStringBuilderClass
                = Class.forName("java.lang.AbstractStringBuilder");
            stringBuilderValue = abstractStringBuilderClass.getDeclaredField("value");
            stringBuilderValue.setAccessible(true);
            stringBuilderCount = abstractStringBuilderClass.getDeclaredField("count");
            stringBuilderCount.setAccessible(true);
        } catch (NoSuchFieldException | ClassNotFoundException e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    public static void save(String fileName, String content) {
        try {
            writeStringToFile(new File(fileName), content);
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError("Cannot save file content: " + fileName, e);
        }
    }

    /**
     * A performance-optimized version of save() that uses reflection to access private fields of
     * StringBuilder.
     */
    public static void save(String fileName, StringBuilder content) {
        try {
            Files.createDirectories(Paths.get(fileName).getParent());

            try (Writer writer = new BufferedWriter(new FileWriter(fileName))){
                toWriter(content, writer);
            }
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError("Cannot save file content: " + fileName, e);
        }
    }

    public static void toWriter(StringBuilder content, Writer writer) throws IOException {
        try {
            char[] sbValue = (char[]) stringBuilderValue.get(content);
            int sbCount = (int) stringBuilderCount.get(content);
            writer.write(sbValue, 0, sbCount);
        } catch (IllegalAccessException e) {
            throw new IllegalStateException(e);
        }
    }

    /**
     * Get language name in uppercase (main module name) given the filename of definition.
     */
    public static String getMainModule(String filename) {
        return FilenameUtils.getBaseName(filename).toUpperCase();
    }

    public static String getFileContent(String file) {
        try {
            return readFileToString(new File(file));
        } catch (FileNotFoundException e) {
            GlobalSettings.kem.registerCriticalError(
                    "Cannot retrieve file content. Make sure that file: " + file + " exists.", e);
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError(
                    "Cannot retrieve file content. An IO error occured: " + file, e);
        }
        return "";
    }

    public static byte[] getFileContentAsBytes(String file) {
        try {
            return FileUtils.readFileToByteArray(new File(file));
        } catch (FileNotFoundException e) {
            GlobalSettings.kem.registerCriticalError(
                    "Cannot retrieve file content. Make sure that file: " + file + " exists.", e);
        } catch (IOException e) {
            GlobalSettings.kem.registerCriticalError(
                    "Cannot retrieve file content. An IO error occured: " + file, e);
        }
        throw new AssertionError("unreachable");
    }

    // create a file with the specified name, create parent directory if it doesn't exist
    public static File createFile(String file) {
            File file1 = new File(file);
            File f2 = new File(file1.getParent());
            f2.mkdirs();
            return file1;
    }

    // generate an unique name for a folder with the name dirName
    public static String generateUniqueFolderName(String dirName) {
        DateFormat df = new SimpleDateFormat("-yyyy-MM-dd-HH-mm-ss-");
        Date today = Calendar.getInstance().getTime();
        String reportDate = df.format(today);
        return dirName + reportDate + UUID.randomUUID().toString();
    }

    /**
     * Loads the properties from the given file into the given Properties object.
     */
    public static void loadProperties(Properties properties, Class<?> cls, String resourcePath) throws IOException {
        InputStream inStream = cls.getResourceAsStream(resourcePath);
        if (inStream == null) {
            throw new IOException("Could not find resource " + resourcePath);
        }
        properties.load(inStream);
    }
}
