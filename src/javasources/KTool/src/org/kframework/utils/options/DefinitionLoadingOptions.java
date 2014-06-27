// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import java.io.File;
import java.io.FilenameFilter;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;

public class DefinitionLoadingOptions {
    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the kompiled " +
            "K definition resides. The default is the unique, only directory with the suffix '-kompiled' " +
            "in the current directory. A definition may also be specified with the 'KRUN_COMPILED_DEF' " +
            "environment variable, in which case it is used if the option is not specified on the command line.")
    private File definition;
    
    public File definition() {
        if (definition == null) {
            if (System.getenv("KRUN_COMPILED_DEF") != null) {
                definition = new File(System.getenv("KRUN_COMPILED_DEF"));
            } else {
                File[] dirs = new File(".").listFiles(new FilenameFilter() {
                    @Override
                    public boolean accept(File current, String name) {
                        return new File(current, name).isDirectory();
                    }
                });
    
                for (int i = 0; i < dirs.length; i++) {
                    if (dirs[i].getAbsolutePath().endsWith("-kompiled")) {
                        if (definition != null) {
                            throw new ParameterException("Multiple compiled definitions found in the "
                                    + "current working directory: " + definition.getAbsolutePath() + " and " +
                                    dirs[i].getAbsolutePath());
                        } else {
                            definition = dirs[i];
                        }
                    }
                }
                
                if (definition == null) {
                    throw new ParameterException("Could not find a compiled definition. " +
                            "Use --directory to specify one.");
                }
            }
        }
        if (!definition.isDirectory()) {
            throw new ParameterException("Does not exist or not a directory: " + definition.getAbsolutePath());
        }
        return definition;
    }
}
