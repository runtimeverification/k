// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

import java.io.Serializable;

public class BackendOptions implements Serializable {

    public BackendOptions() {}

    @Parameter(names="--dry-run", description="Compile program into KORE format but do not run. Only used in Haskell and LLVM backend.")
    public boolean dryRun = false;
}
