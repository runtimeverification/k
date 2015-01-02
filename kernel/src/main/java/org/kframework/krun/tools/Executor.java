// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun.tools;

import org.kframework.backend.unparser.PrintSearchResult;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Cell;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.parser.TermLoader;
import org.kframework.transformation.Transformation;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;
import com.google.inject.Provider;

public interface Executor {


    /**
    Execute a term in normal execution mode until it cannot rewrite any further
    @param cfg The term to rewrite
    @return An object containing both metadata about krun's execution, and information about
    the exit state of the execution
    @exception KRunExecutionException Thrown if the backend fails to successfully execute the
    term
    */
    public abstract KRunState run(Term cfg) throws KRunExecutionException;

    /**
    Perform a breadth-first search of the transition system starting at a particular term.
    @param bound The maximum number of search results to return; null if unbounded
    @param depth The maximum number of transitions to make before terminating; null if
    unbounded
    @param searchType Represents the types of result states to return
    @param pattern A kompiled rule without rewrites (i.e. a pattern and a side condition) to
    use to determine whether a particular state is a search result
    @param cfg The term to begin the search at
    @param compilationInfo the object used to kompile the search pattern, which contains
    metadata used to pretty-print results
    @exception KRunExecutionException Thrown if the backend fails to successfully perform the
    search
    @return An object containing both metadata about krun's execution, and information about
    the results of the search
    */
    public abstract SearchResults search(Integer bound, Integer depth, SearchType searchType, Rule pattern, Term cfg, RuleCompilerSteps compilationInfo) throws KRunExecutionException;

    /**
    Execute a term in normal-execution mode for a specified number of steps
    @param cfg The K term to rewrite
    @param steps The maximum number of transitions to execute for (zero if you want to rewrite
    only until the first transition)
    @exception KRunExecutionException Thrown if the backend fails to successfully execute the
    term
    @exception UnsupportedOperationException The backend implementing this interface does not
    support bounded stepping
    @return An object containing both metadata about krun's execution, and information about
    the resulting term after executing the specified number of steps (or fewer if no further
    rewrites are possible)
    */
    public abstract KRunState step(Term cfg, int steps) throws KRunExecutionException;

    public static class Tool implements Transformation<Void, KRunResult> {

        private final KRunOptions options;
        private final Provider<Term> initialConfiguration;
        private final Context context;
        private final Stopwatch sw;
        private final KExceptionManager kem;
        private final Executor executor;
        private final TermLoader loader;

        @Inject
        Tool(
                KRunOptions options,
                @Main Provider<Term> initialConfiguration,
                Stopwatch sw,
                @Main Context context,
                KExceptionManager kem,
                @Main Executor executor,
                TermLoader loader) {
            this.options = options;
            this.initialConfiguration = initialConfiguration;
            this.context = context;
            this.sw = sw;
            this.kem = kem;
            this.executor = executor;
            this.loader = loader;
        }

        public KRunResult run(Void v, Attributes a) {
            a.add(Context.class, context);
            a.add(Boolean.class, PrintSearchResult.IS_DEFAULT_PATTERN, options.pattern == null);
            try {
                if (options.search()) {
                    return search();
                } else {
                    return execute();
                }
            } catch (KRunExecutionException e) {
                throw KExceptionManager.criticalError(e.getMessage(), e);
            }
        }

        public class SearchPattern {
            public final RuleCompilerSteps steps;
            public final Rule patternRule;

            public SearchPattern(ASTNode pattern) {
                steps = new RuleCompilerSteps(context, kem);
                try {
                    pattern = steps.compile(new Rule((Sentence) pattern), null);
                } catch (CompilerStepDone e) {
                    pattern = (ASTNode) e.getResult();
                }
                patternRule = new Rule((Sentence) pattern);
                sw.printIntermediate("Parsing search pattern");
            }
        }

        public SearchResults search() throws ParseFailedException, KRunExecutionException {
            ASTNode pattern = pattern();
            SearchPattern searchPattern = new SearchPattern(pattern);
            SearchResults result;
            result = executor.search(
                        options.bound,
                        options.depth,
                        options.searchType(),
                        searchPattern.patternRule,
                        initialConfiguration.get(), searchPattern.steps);

            sw.printIntermediate("Search total");
            return result;
        }

        public KRunResult execute() throws ParseFailedException, KRunExecutionException {
            KRunState result;
            if (options.depth != null) {
                result = executor.step(initialConfiguration.get(), options.depth);
                sw.printIntermediate("Bounded execution total");
            } else {
                result = executor.run(initialConfiguration.get());
                sw.printIntermediate("Normal execution total");
            }
            ASTNode pattern = pattern();
            if (pattern != null && !options.search()) {
                SearchPattern searchPattern = new SearchPattern(pattern);
                Term res = result.getRawResult();
                return executor.search(1, 1, SearchType.FINAL, searchPattern.patternRule, res, searchPattern.steps);
            }
            return result;
        }

        public ASTNode pattern() throws ParseFailedException {
            String pattern = options.pattern;
            if (pattern == null && !options.search()) {
                //user did not specify a pattern and it's not a search, so
                //we should return null to indicate no pattern is needed
                return null;
            }
            if (pattern != null && (options.experimental.prove != null || options.experimental.ltlmc())) {
                throw KExceptionManager.criticalError("Pattern matching is not supported by model checking or proving");
            }
            String patternToParse = pattern;
            if (pattern == null) {
                patternToParse = KRunOptions.DEFAULT_PATTERN;
            }
            if (patternToParse.equals(KRunOptions.DEFAULT_PATTERN)) {
                Sentence s = new Sentence();
                s.setBody(new Cell("generatedTop", new Variable("B", Sort.BAG)));
                s.addAttribute(Attribute.ANYWHERE);
                return s;
            }
            return loader.parsePattern(
                    patternToParse,
                    null,
                    Sort.BAG,
                    context);
        }

        @Override
        public String getName() {
            return "concrete execution";
        }
    }
}
