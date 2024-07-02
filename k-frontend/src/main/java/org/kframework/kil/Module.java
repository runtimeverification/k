// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil;

import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Base64;
import java.util.List;

/** A module. */
public class Module extends DefinitionItem {
  private String name;
  private List<ModuleItem> items = new ArrayList<>();

  public Module() {
    super();
  }

  public Module(String name) {
    super();
    this.name = name;
  }

  public void appendModuleItem(ModuleItem item) {
    this.items.add(item);
  }

  public void setName(String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public void setItems(List<ModuleItem> items) {
    this.items = items;
  }

  public List<ModuleItem> getItems() {
    return items;
  }

  @Override
  public void toString(StringBuilder sb) {
    sb.append("module ").append(name).append(" ").append(getAttributes()).append("\n");
    for (ModuleItem i : items) {
      i.toString(sb);
      sb.append("\n");
    }
    sb.append("endmodule");
  }

  /**
   * Used to determine if a module was modified. <a
   * href="https://github.com/runtimeverification/k/issues/2910">GH #2910</a> This allows for
   * scripts to move files around after compilation but still give error messages if the contents of
   * modules differ.
   */
  public String digest() {
    try {
      StringBuilder mod = new StringBuilder();
      toString(mod);
      MessageDigest messageDigest = MessageDigest.getInstance("SHA-256");
      messageDigest.update(mod.toString().getBytes());

      var textDigest = Base64.getEncoder().encode(messageDigest.digest());
      return new String(textDigest);
    } catch (NoSuchAlgorithmException e) {
      throw new RuntimeException(e);
    }
  }
}
