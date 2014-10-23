// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.ksimulation;

import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Spec;

import com.google.inject.Inject;
import com.google.inject.Provider;

public class Simulator implements Transformation<Void, KRunResult<?>> {

    private final KExceptionManager kem;

    @Inject
    Simulator(
            @Main SymbolicRewriter impl,
            @Spec SymbolicRewriter spec,
            @Main Provider<org.kframework.kil.Term> implTerm,
            @Spec Provider<org.kframework.kil.Term> specTerm,
            @Main GlobalContext implGlobalContext,
            @Spec GlobalContext specGlobalContext,
            KExceptionManager kem) {
        this.kem = kem;
    }

    @Override
    public KRunProofResult<?> run(Void v, Attributes a) {
        throw KExceptionManager.criticalError("--simulation is not currently supported");
    }

    @Override
    public String getName() {
        return "--simulation";
    }
}
