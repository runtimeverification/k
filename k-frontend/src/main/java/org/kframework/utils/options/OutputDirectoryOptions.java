// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import java.io.Serializable;

public class OutputDirectoryOptions implements Serializable {

  public OutputDirectoryOptions() {}

  @Inject
  public OutputDirectoryOptions(Void v) {}

  @Parameter(
      names = {"--output-definition", "-o"},
      description = "Path to the exact directory in which the output resides.",
      descriptionKey = "path")
  public String outputDirectory;
}
