// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.backend.kore;

public class ModuleToKOREOptions {
    private boolean heatCoolToEquations;

    public ModuleToKOREOptions() {this(false);}

    public ModuleToKOREOptions(boolean heatCoolToEquations) {
        this.heatCoolToEquations = heatCoolToEquations;
    }

    public boolean isHeatCoolToEquations() {
        return heatCoolToEquations;
    }
}
