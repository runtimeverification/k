// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import com.google.inject.Inject;

public class KilFactory {

    private final KILtoBackendJavaKILTransformer transformer;

    @Inject
    public KilFactory(KILtoBackendJavaKILTransformer transformer) {
        this.transformer = transformer;
    }

    /**
     * Translates a term from the generic KIL representation (
     * {@link org.kframework.kil.Term}) to Java Rewrite Engine internal
     * representation ({@link org.kframework.backend.java.kil.Term}) and
     * evaluates pending functions.
     */
    public Term transformAndEval(org.kframework.kil.Term kilTerm) {
      return transformer.transformAndEval(kilTerm);
    }
}
