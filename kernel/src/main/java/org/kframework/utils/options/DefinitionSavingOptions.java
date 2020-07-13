// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

public class DefinitionSavingOptions {

    public DefinitionSavingOptions() {}

    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output will reside. " +
            "An output can be either a kompiled K definition or a document which depends on the type of backend. " +
            "The default is the directory containing the main definition file.")
    public String directory;

    public DefinitionSavingOptions(String dir) {
        this.directory = dir;
    }
}
