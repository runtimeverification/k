// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.haskell;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class HaskellKompileOptions {

    @Inject
    public HaskellKompileOptions() {}
    @Parameter(names="--haskell-backend-command", description="Command to run the Haskell backend execution engine.", descriptionKey = "command", hidden = true)
    public String haskellBackendCommand = "kore-exec";

    @Parameter(names="--no-haskell-binary", description="Use the textual KORE format in the haskell backend instead of the binary KORE format. This is a development option, but may be necessary on MacOS due to known issues with the binary format.")
    public boolean noHaskellBinary = false;
}
