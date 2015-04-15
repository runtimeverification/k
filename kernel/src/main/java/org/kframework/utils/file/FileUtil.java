// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.utils.file;

import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.util.Providers;
import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

import javax.annotation.Nullable;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.Reader;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Properties;
import java.util.UUID;

@RequestScoped
public class FileUtil {

    private final File tempDir;
    private final Provider<File> kompiledDir;
    private final File workingDir;
    private final Provider<File> definitionDir;
    private final GlobalOptions options;

    @Inject
    public FileUtil(
            @TempDir File tempDir,
            @DefinitionDir @Nullable Provider<File> definitionDir,
            @WorkingDir File workingDir,
            @KompiledDir @Nullable Provider<File> kompiledDir,
            GlobalOptions options) {
        this.tempDir = tempDir;
        this.definitionDir = definitionDir;
        this.workingDir = workingDir;
        this.kompiledDir = kompiledDir;
        this.options = options;
    }

    public static FileUtil testFileUtil() {
        File workingDir = new File(".");
        return new FileUtil(workingDir, Providers.of(workingDir), workingDir, Providers.of(workingDir), new GlobalOptions());
    }

    public void deleteTempDir() {
        if (!options.debug) {
            try {
                FileUtils.deleteDirectory(tempDir);
            } catch (IOException e) {
                throw KExceptionManager.criticalError("Failed to delete temporary directory", e);
            }
        }
    }

    /**
     * Get language name in uppercase (main module name) given the filename of definition.
     */
    public static String getMainModule(String filename) {
        return FilenameUtils.getBaseName(filename).toUpperCase();
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
        try (InputStream inStream = cls.getResourceAsStream(resourcePath)) {
            if (inStream == null) {
                throw new IOException("Could not find resource " + resourcePath);
            }
            properties.load(inStream);
        }
    }

    public void saveToDefinitionDirectory(String file, String content) {
        save(resolveDefinitionDirectory(file), content);
    }

    public String loadFromWorkingDirectory(String file) {
        return load(resolveWorkingDirectory(file));
    }

    public void saveToWorkingDirectory(String file, String content) {
        save(resolveWorkingDirectory(file), content);
    }

    public String loadFromKompiled(String file) {
        return load(resolveKompiled(file));
    }

    public void saveToKompiled(String file, String content) {
        save(resolveKompiled(file), content);
    }

    public String loadFromTemp(String file) {
        return load(resolveTemp(file));
    }

    public void saveToTemp(String file, String content) {
        save(resolveTemp(file), content);
    }

    public String loadFromKBase(String file) {
        return load(resolveKBase(file));
    }

    public File resolveTemp(String file) {
        return new File(tempDir, file);
    }

    public File resolveKompiled(String file) {
        return new File(kompiledDir.get(), file);
    }

    public File resolveDefinitionDirectory(String file) {
        return new File(definitionDir.get(), file);
    }

    public File resolveWorkingDirectory(String file) {
        File f = new File(file);
        if (f.isAbsolute()) return f;
        return new File(workingDir, file);
    }

    public File resolveKBase(String file) {
        return new File(JarInfo.getKBase(), file);
    }

    public void copyTempFileToDefinitionDirectory(String fromPath) {
        copyFileToDirectory(resolveTemp(fromPath), resolveDefinitionDirectory("."));
    }

    public void copyTempFileToKompiledDirectory(String fromPath) {
        copyFileToDirectory(resolveTemp(fromPath), resolveKompiled("."));
    }

    public void copyTempFileToKompiledFile(String fromPath, String toPath) {
        copyFile(resolveTemp(fromPath), resolveKompiled(toPath));
    }

    private void copyFile(File from, File to) {
        try {
            FileUtils.copyFile(from, to);
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not copy " + from + " to " + to, e);
        }
    }

    private void copyFileToDirectory(File from, File toDir) {
        try {
            FileUtils.copyFileToDirectory(from, toDir);
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not copy " + from + " to directory " + toDir, e);
        }
    }

    public static void save(File file, String content) {
        try {
            File dir = file.getAbsoluteFile().getParentFile();
            if (!dir.exists() && !dir.mkdirs()) {
                throw KExceptionManager.criticalError("Could not create directory " + dir);
            }
            FileUtils.writeStringToFile(file, content);
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not write to file " + file.getAbsolutePath(), e);
        }
    }

    private static String load(File file) {
        try {
            return FileUtils.readFileToString(file);
        } catch (IOException e) {
            throw KExceptionManager.criticalError("Could not read from file " + file.getAbsolutePath(), e);
        }
    }

    public static Pair<PipedInputStream, PipedOutputStream> pipeOutputToInput() {
        try {
            PipedOutputStream out = new PipedOutputStream();
            PipedInputStream in = new PipedInputStream(out);
            return Pair.of(in, out);
        } catch (IOException e) {
            throw KExceptionManager.internalError("Error creating input/output pipe", e);
        }
    }

    public static Pair<PipedOutputStream, PipedInputStream> pipeInputToOutput() {
        try {
            PipedInputStream in = new PipedInputStream();
            PipedOutputStream out = new PipedOutputStream(in);
            return Pair.of(out, in);
        } catch (IOException e) {
            throw KExceptionManager.internalError("Error creating input/output pipe", e);
        }
    }

    public static String read(Reader reader) {
        try {
            return IOUtils.toString(reader);
        } catch (IOException e) {
            throw KExceptionManager.internalError("Error reading from " + reader, e);
        }
    }

    public Reader readFromWorkingDirectory(String path) {
        File f = resolveWorkingDirectory(path);
        try {
            return new FileReader(f);
        } catch (FileNotFoundException e) {
            throw KExceptionManager.criticalError("Could not read from file " + f.getAbsolutePath(), e);
        }
    }
}
