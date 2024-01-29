// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import java.util.ArrayList;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;

public class ModulePipeline {
  private ArrayList<ModuleTransformer> passes;

  ModulePipeline() {}

  public void add(ModuleTransformer pass) {
    passes.add(pass);
  }

  public Module apply(Module mod) {
    for (var pass : passes) {
      mod = pass.apply(mod);
    }

    return mod;
  }
}
