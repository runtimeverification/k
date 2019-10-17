// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;

@RequestScoped
public class HaskellKRunOptions {

    @Parameter(names="--dry-run", description="Compile program into KORE format but do not run. Only used in Haskell backend.")
    public boolean dryRun = false;

    @Parameter(names="--haskell-backend-command", description="Command to run the Haskell backend execution engine.")
    public String haskellBackendCommand = "kore-exec";

    @Parameter(names="--haskell-backend-home", description="Directory where the Haskel backend source installation resides.")
    public String haskellBackendHome = System.getenv("KORE_HOME");

    @Parameter(names="--default-claim-type", converter = SentenceTypeConverter.class, description="Default type for claims. Values: [all-path|one-path].")
    public ModuleToKORE.SentenceType defaultClaimType = ModuleToKORE.SentenceType.ONE_PATH;

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
