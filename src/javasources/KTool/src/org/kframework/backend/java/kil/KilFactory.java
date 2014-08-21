// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.utils.general.IndexingStatistics;

import com.google.inject.Inject;

public class KilFactory {

    private final Definition definition;
    private final JavaExecutionOptions options;
    private final KILtoBackendJavaKILTransformer transformer;

    @Inject
    public KilFactory(
            Definition definition,
            JavaExecutionOptions options,
            KILtoBackendJavaKILTransformer transformer) {
        this.definition = definition;
        this.options = options;
        this.transformer = transformer;
    }

    /**
     * Translates a term from the generic KIL representation ({@link org.kframework.kil.Term}) to
     * Java Rewrite Engine internal representation ({@link org.kframework.backend.java.kil.Term}).
     */
    public Term term(org.kframework.kil.Term kilTerm) {
      if (options.indexingStats){
          IndexingStatistics.kilTransformationStopWatch.start();
      }

      Term term = transformer.transformTerm(kilTerm, definition);

      if (options.indexingStats){
          IndexingStatistics.kilTransformationStopWatch.stop();
      }
      return term;
    }
}
