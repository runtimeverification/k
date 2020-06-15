// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.StringUtil;

/** A require directive */
public class Require extends DefinitionItem {
    /** The string argument to {@code require}, as written in the input file. */
    private String value;

    public Require(String value) {
        super();
        this.value = value;
    }

    public void setValue(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("require ");
        sb.append(StringUtil.enquoteCString(value));
    }
}
