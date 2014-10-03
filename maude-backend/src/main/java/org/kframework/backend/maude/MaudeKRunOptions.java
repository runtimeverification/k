// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.kframework.utils.options.OnOffConverter;

import com.beust.jcommander.Parameter;

public class MaudeKRunOptions {

    @Parameter(names="--log-io", description="Make the IO server create logs.", arity=1, converter=OnOffConverter.class)
    public boolean logIO;

    @Parameter(names="--trace", description="Turn on maude trace.")
    public boolean trace = false;

    @Parameter(names="--profile", description="Turn on maude profiler.")
    public boolean profile = false;
}
