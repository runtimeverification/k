// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

/** An import directive */
public class Import extends ModuleItem {

    String name;
    boolean isPublic;
    String tag;

    public Import(String importName, boolean isPublic, String tag) {
        super();
        name = importName;
        this.isPublic = isPublic;
        this.tag = tag;
    }

    public Import(String importName, boolean isPublic, String tag, Location loc, Source source) {
        super(loc, source);
        this.name = importName;
        this.isPublic = isPublic;
        this.tag = tag;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("  imports ");
        if (!isPublic) {
          sb.append("private ");
        } else {
          sb.append("public ");
        }
        sb.append(name);
        if (tag != null) {
          sb.append(".").append(tag);
        }
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public boolean isPublic() {
        return isPublic;
    }

    public void setPublic(boolean isPublic) {
        this.isPublic = isPublic;
    }

    public String getTag() {
        return tag;
    }

    public void setTag() {
        this.tag = tag;
    }
}
