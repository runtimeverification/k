// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.file;

import com.google.inject.Inject;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.Reader;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.Calendar;
import java.util.Date;
import java.util.Map;
import java.util.UUID;
import javax.annotation.Nullable;
import org.apache.commons.io.FileUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class FileUtil {

  private final File tempDir;
  private final File kompiledDir;
  private final File workingDir;
  private final GlobalOptions options;
  private final Map<String, String> env;

  @Inject
  public FileUtil(
      @TempDir File tempDir,
      @WorkingDir File workingDir,
      @KompiledDir @Nullable File kompiledDir,
      GlobalOptions options,
      @Environment Map<String, String> env) {
    this.tempDir = tempDir;
    this.workingDir = workingDir;
    this.kompiledDir = kompiledDir;
    this.options = options;
    this.env = env;
  }

  public static FileUtil testFileUtil() {
    File workingDir = new File(".");
    return new FileUtil(workingDir, workingDir, workingDir, new GlobalOptions(), System.getenv());
  }

  public ProcessBuilder getProcessBuilder() {
    ProcessBuilder pb = new ProcessBuilder().directory(workingDir);
    pb.environment().clear();
    pb.environment().putAll(env);
    return pb;
  }

  public Map<String, String> getEnv() {
    return env;
  }

  public void deleteTempDir(KExceptionManager kem) {
    if (!options.debug()) {
      try {
        FileUtils.deleteDirectory(tempDir);
      } catch (IOException e) {
        kem.registerCriticalWarning(
            ExceptionType.UNDELETED_TEMP_DIR, "Failed to delete temporary directory", e);
      }
    }
  }

  // generate an unique name for a folder with the name dirName
  public static String generateUniqueFolderName(String dirName) {
    DateFormat df = new SimpleDateFormat("-yyyy-MM-dd-HH-mm-ss-SSS-");
    Date today = Calendar.getInstance().getTime();
    String reportDate = df.format(today);
    return dirName + reportDate + UUID.randomUUID();
  }

  public void saveToDefinitionDirectory(String file, String content) {
    save(resolveDefinitionDirectory(file), content);
  }

  public String loadFromWorkingDirectory(String file) {
    return load(resolveWorkingDirectory(file));
  }

  public void saveToWorkingDirectory(String file, byte[] content) {
    save(resolveWorkingDirectory(file), content);
  }

  public void saveToKompiled(String file, String content) {
    save(resolveKompiled(file), content);
  }

  public void saveToTemp(String file, String content) {
    save(resolveTemp(file), content);
  }

  public String loadFromKIncludeDir(String file) {
    return load(resolveKInclude(file));
  }

  public File resolveTemp(String file) {
    if (!tempDir.exists() && !tempDir.mkdirs()) {
      throw KEMException.criticalError("Could not create temporary directory " + tempDir);
    }
    return new File(tempDir, file);
  }

  public File resolveKompiled(String file) {
    return new File(kompiledDir, file);
  }

  public File resolveDefinitionDirectory(String file) {
    return kompiledDir == null ? null : new File(kompiledDir.getParentFile(), file);
  }

  public File resolveWorkingDirectory(String file) {
    return resolveWorkingDirectory(new File(file));
  }

  public File resolveWorkingDirectory(File file) {
    if (file.isAbsolute()) return file;
    return new File(workingDir, file.getPath());
  }

  public File resolveKInclude(String file) {
    return new File(JarInfo.getKIncludeDir().toFile(), file);
  }

  public static void save(File file, String content) {
    try {
      File dir = file.getAbsoluteFile().getParentFile();
      if (!dir.exists() && !dir.mkdirs()) {
        throw KEMException.criticalError("Could not create directory " + dir);
      }
      FileUtils.writeStringToFile(file, content);
    } catch (IOException e) {
      throw KEMException.criticalError("Could not write to file " + file.getAbsolutePath(), e);
    }
  }

  public static void save(File file, byte[] content) {
    try {
      File dir = file.getAbsoluteFile().getParentFile();
      if (!dir.exists() && !dir.mkdirs()) {
        throw KEMException.criticalError("Could not create directory " + dir);
      }
      FileUtils.writeByteArrayToFile(file, content);
    } catch (IOException e) {
      throw KEMException.criticalError("Could not write to file " + file.getAbsolutePath(), e);
    }
  }

  public static String load(File file) {
    try {
      return FileUtils.readFileToString(file);
    } catch (IOException e) {
      throw KEMException.criticalError("Could not read from file " + file.getAbsolutePath(), e);
    }
  }

  public static byte[] loadBytes(File file) {
    try {
      return FileUtils.readFileToByteArray(file);
    } catch (IOException e) {
      throw KEMException.criticalError("Could not read from file " + file.getAbsolutePath(), e);
    }
  }

  public static String read(Reader reader) {
    try {
      return IOUtils.toString(reader);
    } catch (IOException e) {
      throw KEMException.internalError("Error reading from " + reader, e);
    }
  }

  public Reader readFromWorkingDirectory(String path) {
    File f = resolveWorkingDirectory(path);
    try {
      return new FileReader(f);
    } catch (FileNotFoundException e) {
      throw KEMException.criticalError("Could not read from file " + f.getAbsolutePath(), e);
    }
  }
}
