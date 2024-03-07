// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;

public class DefinitionLoadingOptions {

  public DefinitionLoadingOptions() {}

  @Parameter(
      names = {"--definition", "-d"},
      description = "Exact path to the kompiled directory.",
      descriptionKey = "path")
  public String inputDirectory;
}
