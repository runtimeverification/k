// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.helper;

public class TreeNode {

    private String name;
    private String content;

    public TreeNode() {
    }

    public TreeNode(String name) {
        this.name = name;
    }

    public TreeNode(String name, String content) {
        this.setName(name);
        this.setContent(content);
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getContent() {
        return content;
    }

    public void setContent(String content) {
        this.content = content;
    }

    @Override
    public String toString() {
        return this.name;
    }

}