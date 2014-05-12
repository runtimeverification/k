// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.w3c.dom.Element;

public class Location extends Attribute {
    public Location(Element elm) {
        super(elm);
    }
    String filename;
    int lineNumber;
    int columnNumber;
    int startOffset;
    int endOffset;
    
}
