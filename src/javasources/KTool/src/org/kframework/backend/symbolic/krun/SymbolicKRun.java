package org.kframework.backend.symbolic.krun;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.maude.krun.MaudeKRun;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.api.TestGenResults;
import org.kframework.krun.api.Transition;
import org.kframework.utils.Stopwatch;

import java.util.Set;

/**
 * Created by andrei.arusoaie on 4/15/14.
 * This class implements the KRun interface for the symbolic backend.
 */
public class SymbolicKRun implements KRun {

    private Context context;
    KRun runner;

    public SymbolicKRun(Context context, Stopwatch sw) {
        this.context = context;
        this.runner = new MaudeKRun(context, sw);
    }

    @Override
    public KRunResult<KRunState> run(Term cfg) throws KRunExecutionException {
        return runner.run(cfg);
    }

    @Override
    public KRunResult<SearchResults> search(Integer bound, Integer depth, SearchType searchType, Rule pattern, Term cfg, RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        return runner.search(bound, depth, searchType, pattern, cfg, compilationInfo);
    }

    @Override
    public KRunResult<TestGenResults> generate(Integer bound, Integer depth, SearchType searchType, Rule pattern, Term cfg, RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        throw new UnsupportedOperationException("test case generation");
    }

    @Override
    public KRunProofResult<DirectedGraph<KRunState, Transition>> modelCheck(Term formula, Term cfg) throws KRunExecutionException {
        return runner.modelCheck(formula, cfg);
    }

    @Override
    public KRunResult<KRunState> step(Term cfg, int steps) throws KRunExecutionException {
        return runner.step(cfg, steps);
    }

    @Override
    public KRunDebugger debug(Term cfg) throws KRunExecutionException {
        return runner.debug(cfg);
    }

    @Override
    public KRunDebugger debug(DirectedGraph<KRunState, Transition> graph) {
        return runner.debug(graph);
    }

    @Override
    public KRunProofResult<Set<Term>> prove(Module module, Term cfg) throws KRunExecutionException {
        throw  new UnsupportedOperationException("prove reachability rules");
    }

    @Override
    public void setBackendOption(String key, Object value) {

    }
}
