// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.backend.coq;

import com.google.common.collect.ImmutableList;
import com.google.inject.Module;
import org.kframework.main.KModule;

import java.util.List;

/**
 * Created by brandon on 1/21/15.
 */
public class CoqBackendModule implements KModule {
    @Override
    public List<Module> getKDocModules() {
        return ImmutableList.of();
    }

    @Override
    public List<Module> getKompileModules() {
        return ImmutableList.of(new CoqBackendKompileModule());
    }

    @Override
    public List<Module> getKastModules() {
        return ImmutableList.of();
    }

    @Override
    public List<Module> getKRunModules(List<Module> definitionSpecificModules) {
        return ImmutableList.of();
    }

    @Override
    public List<Module> getDefinitionSpecificKRunModules() {
        return ImmutableList.of();
    }

    @Override
    public List<Module> getKTestModules() {
        return ImmutableList.of();
    }
}
