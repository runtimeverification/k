// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun.tools;

import java.util.Set;

import org.kframework.attributes.Source;
import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.parser.TermLoader;
import org.kframework.transformation.Transformation;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;

public interface Prover {

    /**
     * @param cfg The configuration used to initialize the prover
     */
    public abstract Module preprocess(Module module, Term cfg) throws KRunExecutionException;

    /**
     * Prove a set of reachability rules using Matching Logic.
     * @param module A {@link org.kframework.kil.Module} containing a set of reachability rules to be proven.
     * @exception UnsupportedOperationException The backend implementing this interface does not
     * support proofs
     * @return An object containing metadata about whether the proof succeeded, and a counterexample
     * if it failed.
    */
    public abstract KRunProofResult<Set<Term>> prove(Module module) throws KRunExecutionException;

    public static class Tool implements Transformation<Void, KRunResult> {

        private final KRunOptions options;
        private final Context context;
        private final Stopwatch sw;
        private final Term initialConfiguration;
        private final Prover prover;
        private final FileUtil files;
        private final TermLoader termLoader;

        @Inject
        protected Tool(
                KRunOptions options,
                @Main Context context,
                Stopwatch sw,
                @Main Term initialConfiguration,
                @Main Prover prover,
                @Main FileUtil files,
                @Main TermLoader termLoader) {
            this.options = options;
            this.context = context;
            this.sw = sw;
            this.initialConfiguration = initialConfiguration;
            this.prover = prover;
            this.files = files;
            this.termLoader = termLoader;
        }

        @Override
        public KRunProofResult<Set<Term>> run(Void v, Attributes a) {
            a.add(Context.class, context);
            try {
                String proofFile = options.experimental.prove;
                String content = files.loadFromWorkingDirectory(proofFile);
                Definition parsed = termLoader.parseString(content,
                        Source.apply(files.resolveWorkingDirectory(proofFile).getAbsolutePath()));
                Module mod = parsed.getSingletonModule();
                mod = prover.preprocess(mod, initialConfiguration);
                sw.printIntermediate("Preprocess specification rules");
                KRunProofResult<Set<Term>> result = prover.prove(mod);
                sw.printIntermediate("Proof total");
                return result;
            } catch (KRunExecutionException e) {
                throw KEMException.criticalError(e.getMessage(), e);
            }
        }

        @Override
        public String getName() {
            return "--prove";
        }
    }
}
