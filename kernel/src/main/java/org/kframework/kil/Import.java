// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

/** An import directive */
public class Import extends ModuleItem {

    String name;
    boolean isPublic;

    public Import(String importName, boolean isPublic) {
        super();
        name = importName;
        this.isPublic = isPublic;
    }

    public Import(String importName, boolean isPublic, Location loc, Source source) {
        super(loc, source);
        this.name = importName;
        this.isPublic = isPublic;
    }

    @Override
    public void toString(StringBuilder sb) {
        sb.append("  imports ");
        if (!isPublic) {
          sb.append("private ");
        }
        sb.append(name);
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
}
