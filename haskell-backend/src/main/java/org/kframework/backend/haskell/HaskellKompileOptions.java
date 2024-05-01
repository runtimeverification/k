// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class HaskellKompileOptions {

  @Inject
  public HaskellKompileOptions() {}

  @Parameter(
      names = "--haskell-backend-command",
      description = "Command to run the Haskell backend execution engine.",
      descriptionKey = "command",
      hidden = true)
  public String haskellBackendCommand = "kore-exec";

  @Parameter(
      names = "--no-haskell-binary",
      description =
          "Use the textual KORE format in the haskell backend instead of the binary KORE format."
              + " This flag is disabled by default, except when running on macOS, where it is enabled and cannot be disabled because of a bug in the underlying Haskell libraries.",
      hidden = true)
  public boolean noHaskellBinary = false;
}
