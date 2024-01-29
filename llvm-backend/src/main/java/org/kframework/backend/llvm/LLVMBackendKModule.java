// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.backend.llvm;

import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.multibindings.MapBinder;
import java.util.Collections;
import java.util.List;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.Backend;
import org.kframework.main.AbstractKModule;

/** Created by traiansf on 9/13/18. */
public class LLVMBackendKModule extends AbstractKModule {

  @Override
  public List<Module> getKompileModules() {
    List<Module> mods = super.getKompileModules();
    mods.add(
        new AbstractModule() {
          @Override
          protected void configure() {
            bindOptions(LLVMBackendKModule.this::kompileOptions, binder());

            MapBinder<String, Backend> mapBinder =
                MapBinder.newMapBinder(binder(), String.class, Backend.class);
            mapBinder.addBinding("llvm").to(LLVMBackend.class);
          }
        });
    return mods;
  }

  @Override
  public List<Pair<Class<?>, Boolean>> kompileOptions() {
    return Collections.singletonList(Pair.of(LLVMKompileOptions.class, true));
  }
}
