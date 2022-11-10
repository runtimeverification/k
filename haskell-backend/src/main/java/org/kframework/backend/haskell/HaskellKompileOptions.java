// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class HaskellKompileOptions {

    @Parameter(names="--haskell-backend-command", description="Command to run the Haskell backend execution engine.")
    public String haskellBackendCommand = "kore-exec";

    @Parameter(names="--no-haskell-binary", description="Do not force the haskell backend to use the binary format. Use the textual format instead. This is a development option. Sometime the binary format can cause issues.")
    public boolean noHaskellBinary = false;
}
