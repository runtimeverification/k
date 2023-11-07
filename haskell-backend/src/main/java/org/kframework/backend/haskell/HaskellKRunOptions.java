// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;

@RequestScoped
public class HaskellKRunOptions {
  @Inject
  public HaskellKRunOptions() {}

  @Parameter(
      names = "--haskell-backend-command",
      descriptionKey = "command",
      description = "Command to run the Haskell backend execution engine.",
      hidden = true)
  public String haskellBackendCommand = "kore-exec";

  @Parameter(
      names = "--haskell-backend-home",
      descriptionKey = "directory",
      description = "Directory where the Haskell backend source installation resides.",
      hidden = true)
  public String haskellBackendHome = System.getenv("KORE_HOME");

  @Parameter(
      names = "--default-claim-type",
      descriptionKey = "type",
      converter = SentenceTypeConverter.class,
      description = "Default type for claims. Values: [all-path|one-path].")
  public ModuleToKORE.SentenceType defaultClaimType = ModuleToKORE.SentenceType.ALL_PATH;

  public static class SentenceTypeConverter extends BaseEnumConverter<ModuleToKORE.SentenceType> {

    public SentenceTypeConverter(String optionName) {
      super(optionName);
    }

    @Override
    public Class<ModuleToKORE.SentenceType> enumClass() {
      return ModuleToKORE.SentenceType.class;
    }
  }
}
