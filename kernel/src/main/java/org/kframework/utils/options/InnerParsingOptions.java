// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import java.io.Serializable;

/**
 * Provides the options needed for tools to perform inner parsing of definitions from source.
 *
 * <p>Used currently by kompile, and kprove.
 */
public class InnerParsingOptions implements Serializable {

  public InnerParsingOptions() {}

  @Inject
  public InnerParsingOptions(Void v) {}

  @Parameter(
      names = "--profile-rule-parsing",
      description = "Store in this file time taken in ms to parse each rule in the semantics.",
      descriptionKey = "file",
      hidden = true)
  public String profileRules;

  public enum TypeInferenceMode {
    Z3,
    SIMPLESUB,
    CHECKED,
    // We use an explicit DEFAULT option here so that ParseInModule can set a default which
    // applies even for those codepaths that don't rely on KompileOptions
    DEFAULT,
  }

  @Parameter(
      names = "--type-inference-mode",
      description =
          "Choose between the Z3-based and SimpleSub-based type inference algorithms, or run both"
              + " and check that their results are equal. Must be one of "
              + "[z3|simplesub|checked|default].",
      hidden = true)
  public TypeInferenceMode typeInferenceMode = TypeInferenceMode.DEFAULT;
}
