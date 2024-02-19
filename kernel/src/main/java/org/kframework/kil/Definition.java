// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil;

import com.google.inject.Inject;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/** Represents a language definition. Includes contents from all {@code required}-d files. */
public class Definition extends ASTNode {

  private List<DefinitionItem> items;
  private String mainModule;

  public Map<String, ASTNode> locations = new HashMap<>();

  public Definition() {
    super();
  }

  @Inject
  public Definition(Void v) {}

  @Override
  public void toString(StringBuilder sb) {
    for (DefinitionItem di : items) {
      di.toString(sb);
      sb.append("\n\n");
    }
  }

  public void setItems(List<DefinitionItem> items) {
    this.items = items;
  }

  public List<DefinitionItem> getItems() {
    return items;
  }

  public void setMainModule(String mainModule) {
    this.mainModule = mainModule;
  }

  public String getMainModule() {
    return mainModule;
  }
}
