// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.file;

import org.apache.commons.io.FilenameUtils;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Properties;

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
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot save file content: " + fileName, "internal", "FileUtil.java"));
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
            e.printStackTrace();
            GlobalSettings.kem.register(
                new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                    "Cannot save file content: " + fileName + ", " + e.getMessage(),
                    "internal", "FileUtil.java"));
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
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot retrieve file content. Make sure that file: " + file + " exists.", "internal", "FileUtil.java"));
        } catch (IOException e) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot retrieve file content. An IO error occured: " + file, "internal", "FileUtil.java"));
        }
        return "";
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
        try {
            return File.createTempFile(dirName, "").getName();
        } catch (IOException e) {
            org.kframework.utils.Error.report("Error while generating unique directory name:" + e.getMessage());
        }
        return null;
    }

    /**
     * Loads the properties from the given file into the given Properties object.
     */
    public static void loadProperties(Properties properties, String fileName) throws IOException {
        FileInputStream inStream = new FileInputStream(fileName);
        properties.load(inStream);
    }
}
