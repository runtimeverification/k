// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;

@RequestScoped
public class HaskellKRunOptions {

    @Parameter(names="--haskell-backend-command", description="Command to run the Haskell backend execution engine.")
    public String haskellBackendCommand = "kore-exec";

    @Parameter(names="--haskell-backend-home", description="Directory where the Haskell backend source installation resides.")
    public String haskellBackendHome = System.getenv("KORE_HOME");

    @Parameter(names="--default-claim-type", converter = SentenceTypeConverter.class, description="Default type for claims. Values: [all-path|one-path].")
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
