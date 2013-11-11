package org.kframework.ktest2.Config;

import java.io.File;

public class ConfigFileError extends Throwable {
    public ConfigFileError(File configFile, String err) {
        super("error in xml file " + configFile.getAbsolutePath() + "\n\t" + err);
    }
}
