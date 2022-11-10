package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

import java.io.Serializable;

public class OutputDirectoryOptions implements Serializable {

    public OutputDirectoryOptions() {}

    @Inject
    public OutputDirectoryOptions(Void v) {}

    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the directory containing the main definition file.")
    public String directory;

    @Parameter(names={"--output-definition", "-o"}, description="Path to the exact directory in which the output resides.")
    public String outputDirectory;
}
