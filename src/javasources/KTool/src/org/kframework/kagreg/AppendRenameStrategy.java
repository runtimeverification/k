// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kagreg;

public class AppendRenameStrategy implements RenameStrategy {
    String toAppend;
    
    public AppendRenameStrategy(String toAppend) {
        this.toAppend = toAppend;
    }

    @Override
    public String getNewName(String oldName) {
        return oldName + toAppend;
    }
}
