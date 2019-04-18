// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class HaskellKRunOptions {

    @Parameter(names="--dry-run", description="Compile program into KORE format but do not run. Only used in Haskell backend.")
    public boolean dryRun = false;

    @Parameter(names="--haskell-backend-command", description="Command to run the Haskell backend execution engine.")
    public String haskellBackendCommand = "kore-exec";

    @Parameter(names="--haskell-backend-home", description="Directory where the Haskel backend source installation resides.")
    public String haskellBackendHome = System.getenv("KORE_HOME");

    @Parameter(names="--all-path-reachability", description="Whether to interpret claims as All Path Reachability Claims.")
    public boolean allPathReachability = false;
}