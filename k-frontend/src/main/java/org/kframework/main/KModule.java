// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.main;

import com.google.inject.Module;
import java.util.List;

public interface KModule {

  List<Module> getKompileModules();

  List<Module> getKastModules();

  List<Module> getKProveModules();
}
