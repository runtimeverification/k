// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

public class DefinitionLoadingOptions {

    public DefinitionLoadingOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public DefinitionLoadingOptions(Void v) {}

    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the kompiled " +
            "K definition resides. The default is the unique, only directory with the suffix '-kompiled' " +
            "in the current directory. A definition may also be specified with the 'KRUN_COMPILED_DEF' " +
            "environment variable, in which case it is used if the option is not specified on the command line.")
    public String directory;
}
