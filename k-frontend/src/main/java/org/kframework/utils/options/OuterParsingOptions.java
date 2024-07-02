// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import java.io.File;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

/**
 * Provides the options needed for tools to perform outer parsing of definitions from source.
 *
 * <p>Used currently by kompile, and kdep.
 */
public class OuterParsingOptions implements Serializable {

  public OuterParsingOptions() {}

  @Inject
  public OuterParsingOptions(Void v) {}

  public OuterParsingOptions(File mainDefinitionFile) {
    this.mainDefinitionFile = mainDefinitionFile;
  }

  @Parameter(description = "<file>")
  private String mainParameter;

  private File mainDefinitionFile;

  public synchronized File mainDefinitionFile(FileUtil files) {
    if (mainDefinitionFile == null) {
      if (mainParameter == null) {
        throw KEMException.criticalError(
            "You have to provide exactly one main file in order to do outer parsing.");
      }
      mainDefinitionFile = files.resolveWorkingDirectory(mainParameter);
    }
    return mainDefinitionFile;
  }

  @Parameter(
      names = "-I",
      description = "Add a directory to the search path for requires statements.",
      descriptionKey = "path")
  public List<String> includes = new ArrayList<>();

  @Parameter(
      names = "--no-prelude",
      description = "Do not implicitly require prelude.md.",
      hidden = true)
  public boolean noPrelude = false;

  @Parameter(
      names = "--md-selector",
      description =
          "Preprocessor: for .md files, select only the md code blocks that match the selector"
              + " expression. Ex:'k&(!a|b)'.",
      descriptionKey = "expression")
  public String mdSelector = "k";
}
