// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

public class IndentationOptions {
    private int width;
    private int auxTabSize;
    private int tabSize;

    public IndentationOptions(int width, int auxTabSize, int tabSize) {
        this.width = width;
        this.auxTabSize = auxTabSize;
        this.tabSize = tabSize;
    }

    public IndentationOptions() {
        this.width = 78;
        this.auxTabSize = 2;
        this.tabSize = 1;
    }

    public void setWidth(int width) {
        this.width = width;
    }

    public int getWidth() {
        return width;
    }

    public int getAuxTabSize() {
        return auxTabSize;
    }

    public void setAuxTabSize(int auxTabSize) {
        this.auxTabSize = auxTabSize;
    }

    public int getTabSize() {
        return tabSize;
    }

    public void setTabSize(int tabSize) {
        this.tabSize = tabSize;
    }
}
