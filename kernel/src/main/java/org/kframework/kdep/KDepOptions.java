// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kdep;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.OutputDirectoryOptions;

/**
 * JCommander options for kdep. Essentially, this should contain all the kompile options needed in
 * order to decide what files get slurped by the outer parser.
 */
@RequestScoped
public class KDepOptions {

  @Inject
  public KDepOptions() {}

  @ParametersDelegate public transient GlobalOptions global = new GlobalOptions();

  @ParametersDelegate public OuterParsingOptions outerParsing = new OuterParsingOptions();

  @ParametersDelegate public OutputDirectoryOptions outputDirectory = new OutputDirectoryOptions();

  @Parameter(
      names = "--remake-depend",
      description = "Generate an additional rule to remake the dependency file.")
  public boolean alsoRemakeDepend = false;
}
