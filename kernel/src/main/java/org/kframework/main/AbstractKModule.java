// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.main;

import com.google.common.collect.Lists;
import com.google.inject.AbstractModule;
import com.google.inject.Binder;
import com.google.inject.Module;
import com.google.inject.multibindings.Multibinder;
import java.util.Collections;
import java.util.List;
import java.util.function.Supplier;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.utils.inject.Options;

public abstract class AbstractKModule implements KModule {

  public List<Pair<Class<?>, Boolean>> kompileOptions() {
    return Collections.emptyList();
  }

  public List<Pair<Class<?>, Boolean>> krunOptions() {
    return Collections.emptyList();
  }

  public List<Pair<Class<?>, Boolean>> kproveOptions() {
    return Collections.emptyList();
  }

  protected void bindOptions(Supplier<List<Pair<Class<?>, Boolean>>> action, Binder binder) {
    binder.requireAtInjectOnConstructors();
    Multibinder<Object> optionsBinder =
        Multibinder.newSetBinder(binder, Object.class, Options.class);
    for (Pair<Class<?>, Boolean> option : action.get()) {
      optionsBinder.addBinding().to(option.getKey());
    }
  }

  @Override
  public List<Module> getKompileModules() {
    return Lists.newArrayList(
        new AbstractModule() {

          @Override
          protected void configure() {
            bindOptions(AbstractKModule.this::kompileOptions, binder());
          }
        });
  }

  @Override
  public List<Module> getKastModules() {
    return Lists.newArrayList();
  }

  @Override
  public List<Module> getKProveModules() {
    return Lists.newArrayList(
        new AbstractModule() {

          @Override
          protected void configure() {
            bindOptions(AbstractKModule.this::kproveOptions, binder());
          }
        });
  }
}
