// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.kframework.utils.options.OnOffConverter;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

public class MaudeKRunOptions {

    public MaudeKRunOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public MaudeKRunOptions(Void v) {}

    @Parameter(names="--log-io", description="Make the IO server create logs.", arity=1, converter=OnOffConverter.class)
    public boolean logIO;

    @Parameter(names="--profile", description="Turn on maude profiler.")
    public boolean profile = false;
}
