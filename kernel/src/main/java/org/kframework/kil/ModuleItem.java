// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

public abstract class ModuleItem extends ASTNode {
  public ModuleItem() {
    super();
  }

  public ModuleItem(Location loc, Source source) {
    super(loc, source);
  }
}
