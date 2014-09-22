package org.kframework.backend.java.symbolic;

import java.util.List;

import org.kframework.main.KModule;

import com.google.common.collect.ImmutableList;
import com.google.inject.Module;

public class JavaBackendKModule implements KModule {

    @Override
    public List<Module> getKompileModules() {
        return ImmutableList.<Module>of(
                new JavaSymbolicCommonModule(),
                new JavaSymbolicKompileModule());
    }

    @Override
    public List<Module> getKastModules() {
        return ImmutableList.of();
    }

    @Override
    public List<Module> getKRunModules(List<Module> definitionSpecificModules) {
        JavaExecutionOptions options = new JavaExecutionOptions();
        return ImmutableList.<Module>of(
                new JavaSymbolicKRunModule(options),
                new JavaSymbolicKRunModule.SimulationModule(definitionSpecificModules));
    }

    @Override
    public List<Module> getKTestModules() {
        return ImmutableList.of();
    }

    @Override
    public List<Module> getDefinitionSpecificKRunModules() {
        return ImmutableList.<Module>of(
                new JavaSymbolicKRunModule.CommonModule());
    }

}
