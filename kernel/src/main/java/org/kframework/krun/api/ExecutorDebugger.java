// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun.api;

import com.google.inject.Inject;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.krun.GenericKRunState;
import org.kframework.krun.GenericTransition;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.tools.Debugger;
import org.kframework.krun.tools.Executor;
import org.kframework.parser.TermLoader;
import org.kframework.rewriter.SearchType;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Map.Entry;

public class ExecutorDebugger implements Debugger {
    private Integer currentState;
    private KRunCompactGraph graph;

    private static Rule defaultPattern;
    private static RuleCompilerSteps defaultPatternInfo;

    private final Context context;
    private final Executor executor;
    private final TermLoader loader;
    private final KExceptionManager kem;
    private final KRunState.Counter counter;

    @Inject
    public ExecutorDebugger(
            Executor executor,
            Context context,
            TermLoader loader,
            KExceptionManager kem,
            KRunState.Counter counter) throws KRunExecutionException {
        this.context = context;
        this.executor = executor;
        this.loader = loader;
        this.kem = kem;
        this.counter = counter;
    }

    @Override
    public void start(Term initialConfiguration) throws KRunExecutionException {
        try {
            ASTNode pattern = loader.parsePattern(
                    KRunOptions.DEFAULT_PATTERN,
                    null,
                    Sort.BAG);
            defaultPatternInfo = new RuleCompilerSteps(context, kem);
            pattern = defaultPatternInfo.compile(new Rule((Sentence) pattern), null);

            defaultPattern = (Rule) pattern;
        } catch (CompilerStepDone e) {
            e.printStackTrace();
        }
        KRunState reduced = executor.step(initialConfiguration, 0, false).getFinalState();
        graph = new KRunCompactGraph();
        graph.addVertex(reduced);
        currentState = reduced.getStateId();
    }


    public KRunGraph getGraph() {
        return graph;
    }

    public Integer getCurrentState() {
        return currentState;
    }

    public void setCurrentState(Integer stateNum) throws IllegalArgumentException {
        if (stateNum == null || graph.containsState(stateNum)) {
            currentState = stateNum;
        } else {
            throw new IllegalArgumentException("Cannot set current state to state " + stateNum
                    + ": it does not exist in the graph.");
        }
    }

    @Override
    public KRunState getState(int stateNum) {
        return graph.getState(stateNum);
    }


    public void step(int steps) throws KRunExecutionException {
        if (currentState == null) {
            throw new IllegalStateException("Cannot step without a current state to step from. "
                    + "If you previously used the search command you must"
                    + "first select a solution with the select command before executing steps of rewrites!");
        }
        RewriteRelation finalRelation;
        if (steps >= 0) {
            finalRelation = executor.step(getState(currentState).toBackendTerm(), steps, true);
        } else {
            finalRelation = executor.run(getState(currentState).toBackendTerm(), true);
        }
        KRunGraph currentGraph = finalRelation.getExecutionGraph().get();
        //merge the new graph into the current graph
        graph.mergeSearchGraph(currentGraph);
        KRunState finalState = finalRelation.getFinalState();
        Entry<Integer, KRunState> prevState = graph.containsValue(finalState);
        if (!(prevState == null)) {
            currentState = prevState.getKey();
        } else {
            currentState = finalState.getStateId();
        }
    }

    public void resume() throws KRunExecutionException {
        step(-1);
    }

    public SearchResults stepAll(int steps) throws KRunExecutionException {
        if (currentState == null) {
            throw new IllegalStateException("Cannot step without a current state to step from. "
                    + "If you previously used the search command you must"
                    + "first select a solution with the select command before executing steps of rewrites!");
        }
        SearchResults results = executor.search(null, steps, SearchType.PLUS, defaultPattern, getState(currentState).getRawResult(), defaultPatternInfo, true);
        graph.mergeSearchGraph(results.getGraph());
        currentState = null;
        return results;
    }


    public Transition getEdge(int state1, int state2) {
        KRunState first = getState(state1);
        KRunState second = getState(state2);
        Transition edge = graph.findEdge(first, second);
        if (edge == null)
            throw new IllegalArgumentException("Edge between states "
                    + state1 + " and " + state2 + " does not exist in the current graph");
        return edge;
    }

    public void readFromStdin(String s) {
        if (currentState == null) {
            throw new IllegalStateException("Cannot read from stdin without a current state to step from. "
                    + "If you previously used the search command you must"
                    + "first select a solution with the select command before reading from stdin!");
        }
        Term configuration = getState(currentState).getRawResult();
        AppendToStdin transformer = new AppendToStdin(s, context);
        Term result;
        result = (Term) transformer.visitNode(configuration);
        if (!transformer.getSucceeded()) {
            throw new IllegalStateException("Cannot perform command: Configuration does not " +
                "have an stdin buffer");
        }
        KRunState newState = new GenericKRunState(result, counter);
        Entry<Integer, KRunState> prevValue = graph.containsValue(newState);
        if (prevValue!=null) {
            KRunState canonicalNewState = graph.canonicalizeState(newState);
            Transition edge = graph.findEdge(getState(currentState), canonicalNewState);
            if (edge == null) {
                graph.addEdge(GenericTransition.stdin(s),
                    getState(currentState), canonicalNewState);
            }
            currentState = canonicalNewState.getStateId();
            return;
        }
        graph.addVertex(newState);
        graph.addEdge(GenericTransition.stdin(s),
            getState(currentState), newState);
        currentState = newState.getStateId();
    }

    private static class AppendToStdin extends CopyOnWriteTransformer {
        private String str;
        private boolean succeeded;
        private boolean inStdin, inBuffer;
        public AppendToStdin(String str, Context context) {
            super("Append a string to the stdin buffer", context);
            this.str = str;
            succeeded = false;
            inStdin = false;
            inBuffer = false;
        }

        public boolean getSucceeded() {
            return succeeded;
        }

        @Override
        public ASTNode visit(Cell cell, Void _void)  {
            if ("stdin".equals(context.cells.get(cell.getLabel())
                .getCellAttributes().get("stream"))) {
                inStdin = true;
                ASTNode result = super.visit(cell, _void);
                inStdin = false;
                return result;
            }
            return super.visit(cell, _void);
        }

        @Override
        public ASTNode visit(KApp kapp, Void _void)  {
            if (kapp.getLabel().equals(KLabelConstant.of("'#buffer"))) {
                inBuffer = true;
                ASTNode result = super.visit(kapp, _void);
                inBuffer = false;
                return result;
            }
            return super.visit(kapp, _void);
        }

        @Override
        public ASTNode visit(StringBuiltin s, Void _void)  {
            if (inStdin && inBuffer) {
                succeeded = true;
                return StringBuiltin.of(s.stringValue() + str);
            }
            return super.visit(s, _void);
        }
    }

    @Override
    public void setGraph(KRunGraph graph) {
        this.graph = new KRunCompactGraph(graph);
    }
}
