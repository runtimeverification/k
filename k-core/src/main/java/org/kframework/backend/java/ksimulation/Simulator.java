// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.ksimulation;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;

import com.google.inject.Inject;

public class Simulator implements Transformation<Void, KRunResult<?>> {

    private final Waitor waitor;

    @Inject
    Simulator(Waitor waitor) {
        this.waitor = waitor;
    }

    @Override
    public KRunProofResult<?> run(Void v, Attributes a) {
        waitor.init();
        waitor.start();
        try {
            waitor.join();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return new KRunProofResult<Void>(false, null);
        }
        return new KRunProofResult<Void>(true, null);
    }

    @Override
    public String getName() {
        return "--simulation";
    }
}
