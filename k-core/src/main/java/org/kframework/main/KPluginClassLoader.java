// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import org.apache.commons.io.FilenameUtils;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;

/**
 * A ClassLoader that allows adding JARs in directories.
 */
public class KPluginClassLoader extends URLClassLoader {

    public KPluginClassLoader() {
        super(new URL[0]);
    }

    /**
     * Add JAR files in the path to ClassLoader. Does not traverse sub-directories.
     * @param path Path to directory.
     */
    public void addPath(String path) {
        File root = new File(path);
        File[] fs = root.listFiles();
        if (fs == null) {
            Thread.dumpStack();
            FrontEnd.printBootError(path + " is not a directory or an IO error occured.");
        } else {
            for (File f : fs) {
                if (FilenameUtils.getExtension(f.getPath()).toLowerCase().equals("jar")) {
                    try {
                        addURL(f.toURI().toURL());
                    } catch (MalformedURLException e) {
                        e.printStackTrace();
                        FrontEnd.printBootError(e.getMessage());
                    }
                }
            }
        }
    }
}
