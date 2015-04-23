// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun.tools;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Concrete;
import org.kframework.utils.inject.Main;

import com.beust.jcommander.ParameterException;
import com.google.inject.Inject;

public interface LtlModelChecker {

    /**
    Perform LTL model-checking of a term according to a particular LTL formula
    @param formula A {@link java.lang.String} expressing the LTL formula to check
    @param cfg The initial configuration whose transitions should be model-checked
    @exception KRunExecutionException Thrown if the backend fails to successfully model-check
    the term
    @exception UnsupportedOperationException The backend implementing this interface does not
    support LTL model checking
    @return An object containing both metadata about krun's execution, and a graph containing
    the LTL counterexample if model-checking failed (null if it succeeded)
    */
    public abstract KRunProofResult<KRunGraph> modelCheck(String formula, Term cfg) throws KRunExecutionException;

    public static class Tool implements Transformation<Void, KRunResult> {

        private final KRunOptions options;
        private final Term initialConfiguration;
        private final Context context;
        private final Stopwatch sw;
        private final LtlModelChecker modelChecker;
        private final FileUtil files;
        private final Definition definition;

        @Inject
        protected Tool(
                KRunOptions options,
                @Main Term initialConfiguration,
                @Main Context context,
                Stopwatch sw,
                @Main LtlModelChecker modelChecker,
                @Main FileUtil files,
                @Main(Concrete.class) Definition definition) {
            this.options = options;
            this.initialConfiguration = initialConfiguration;
            this.context = context;
            this.sw = sw;
            this.modelChecker = modelChecker;
            this.files = files;
            this.definition = definition;
        }

        @Override
        public KRunProofResult<KRunGraph> run(Void v, Attributes a) {
            a.add(Context.class, context);
            a.add(Definition.class, definition);
            try {
                KRunProofResult<KRunGraph> result = modelChecker.modelCheck(
                                ltlmc(),
                                initialConfiguration);
                sw.printIntermediate("Model checking total");
                return result;
            } catch (KRunExecutionException e) {
                throw KEMException.criticalError(e.getMessage(), e);
            }
        }

        public String ltlmc() {
            if (options.experimental.ltlmc != null && options.experimental.ltlmcFile != null) {
                throw new ParameterException("You may specify only one of --ltlmc and --ltlmc-file.");
            }
            if (options.experimental.ltlmc != null) {
                return options.experimental.ltlmc;
            }
            if (options.experimental.ltlmcFile == null) {
                return null;
            }
            return files.loadFromWorkingDirectory(options.experimental.ltlmcFile);
        }

        @Override
        public String getName() {
            return "--ltlmc";
        }
    }

}
