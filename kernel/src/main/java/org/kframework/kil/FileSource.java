// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import java.io.File;

public class FileSource implements Source {

    private File file;

    private String path;

    public FileSource(File file) {
        this.file = file;
        this.path = file.getAbsolutePath();
    }

    public File getFile() {
        return file;
    }

    @Override
    public String toString() {
        return "File: " + path;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FileSource that = (FileSource) o;

        if (!path.equals(that.path)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return path.hashCode();
    }
}
