// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.main;

import com.google.inject.Module;

import java.util.List;

public interface KModule {

    List<Module> getKDocModules();
    List<Module> getKompileModules();
    List<Module> getKastModules();
    List<Module> getKRunModules();
    List<Module> getKEqModules(List<Module> definitionSpecificModules);
    List<Module> getDefinitionSpecificKEqModules();
    List<Module> getKProveModules();
}
