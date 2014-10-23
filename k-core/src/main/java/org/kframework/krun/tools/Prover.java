// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.tools;

import java.util.Set;

import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Sources;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.parser.TermLoader;
import org.kframework.transformation.Transformation;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;

public interface Prover {

    /**
     * Prove a set of reachability rules using Matching Logic.
     * @param module A {@link org.kframework.kil.Module} containing a set of reachability rules to be proven.
     * @param cfg The configuration used to initialize the prover
     * @exception UnsupportedOperationException The backend implementing this interface does not
     * support proofs
     * @return An object containing metadata about whether the proof succeeded, and a counterexample
     * if it failed.
    */
    public abstract KRunProofResult<Set<Term>> prove(Module module, Term cfg) throws KRunExecutionException;

    public static class Tool implements Transformation<Void, KRunResult<?>> {

        private final KRunOptions options;
        private final Context context;
        private final Stopwatch sw;
        private final Term initialConfiguration;
        private final KExceptionManager kem;
        private final Prover prover;
        private final FileUtil files;
        private final TermLoader loader;

        @Inject
        protected Tool(
                KRunOptions options,
                @Main Context context,
                Stopwatch sw,
                @Main Term initialConfiguration,
                KExceptionManager kem,
                @Main Prover prover,
                @Main FileUtil files,
                TermLoader loader) {
            this.options = options;
            this.context = context;
            this.sw = sw;
            this.initialConfiguration = initialConfiguration;
            this.kem = kem;
            this.prover = prover;
            this.files = files;
            this.loader = loader;
        }

        @Override
        public KRunProofResult<Set<Term>> run(Void v, Attributes a) {
            a.add(Context.class, context);
            try {
                String proofFile = options.experimental.prove;
                String content = files.loadFromWorkingDirectory(proofFile);
                Definition parsed = loader.parseString(content,
                        Sources.fromFile(proofFile), context);
                Module mod = parsed.getSingletonModule();
                KRunProofResult<Set<Term>> result = prover.prove(mod, initialConfiguration);
                sw.printIntermediate("Proof total");
                return result;
            } catch (KRunExecutionException e) {
                throw KExceptionManager.criticalError(e.getMessage(), e);
            }
        }

        @Override
        public String getName() {
            return "--prove";
        }
    }
}
