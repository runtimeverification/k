// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.tools;

import org.kframework.kil.Attributes;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;

public interface LtlModelChecker {

    /**
    Perform LTL model-checking of a term according to a particular LTL formula
    @param formula The K term expressing the LTL formula to check
    @param cfg The initial configuration whose transitions should be model-checked
    @exception KRunExecutionException Thrown if the backend fails to successfully model-check
    the term
    @exception UnsupportedOperationException The backend implementing this interface does not
    support LTL model checking
    @return An object containing both metadata about krun's execution, and a graph containing
    the LTL counterexample if model-checking failed (null if it succeeded)
    */
    public abstract KRunProofResult<KRunGraph> modelCheck(Term formula, Term cfg) throws KRunExecutionException;

    public static class Tool implements Transformation<Void, KRunResult<?>> {

        private final KRunOptions options;
        private final Term initialConfiguration;
        private final Context context;
        private final Stopwatch sw;
        private final LtlModelChecker modelChecker;
        private final KExceptionManager kem;
        private final RunProcess rp;

        @Inject
        protected Tool(
                KRunOptions options,
                @Main Term initialConfiguration,
                @Main Context context,
                Stopwatch sw,
                @Main LtlModelChecker modelChecker,
                KExceptionManager kem,
                RunProcess rp) {
            this.options = options;
            this.initialConfiguration = initialConfiguration;
            this.context = context;
            this.sw = sw;
            this.modelChecker = modelChecker;
            this.kem = kem;
            this.rp = rp;
        }

        @Override
        public KRunProofResult<KRunGraph> run(Void v, Attributes a) {
            a.add(Context.class, context);
            try {
                Term formula = rp.runParser("kast -e",
                        options.experimental.ltlmc(), false, Sort.of("LtlFormula"), context);
                KRunProofResult<KRunGraph> result = modelChecker.modelCheck(
                                formula,
                                initialConfiguration);
                sw.printIntermediate("Model checking total");
                return result;
            } catch (KRunExecutionException e) {
                throw KExceptionManager.criticalError(e.getMessage(), e);
            }
        }

        @Override
        public String getName() {
            return "--ltlmc";
        }
    }

}
