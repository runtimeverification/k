// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.utils.StringUtil;

public class SyntaxLexical extends ModuleItem {

    public final String name;
    public final String regex;

    public SyntaxLexical(String name, String regex) {
        super();
        this.name = name;
        this.regex = regex;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        SyntaxLexical other = (SyntaxLexical) obj;
        if (!name.equals(other.name))
            return false;
        if (!regex.equals(other.regex))
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + name.hashCode();
        result = prime * result + regex.hashCode();
        return result;
    }

    @Override
    public void toString(StringBuilder sb) {
      sb.append("  syntax lexical ").append(name).append(" = r").append(StringUtil.enquoteKString(regex)).append(" ").append(getAttributes());
    }

}
