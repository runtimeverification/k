// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.File;

public class FileSource implements Source {

    private File file;

    public FileSource(File file) {
        this.file = file;
    }

    public File getFile() {
        return file;
    }

    @Override
    public String toString() {
        return "File: " + file.getAbsolutePath();
    }
}
