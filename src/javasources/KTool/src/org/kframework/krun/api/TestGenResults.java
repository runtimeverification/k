package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;

import java.util.List;
import java.util.Map;

public class TestGenResults {
	private List<TestGenResult> testGenResults;
	private DirectedGraph<KRunState, Transition> graph;
	private boolean isDefaultPattern;

    protected Context context;

	public TestGenResults(List<TestGenResult> results,
			DirectedGraph<KRunState, Transition> graph,
			boolean isDefaultPattern, Context context) {
        this.context = context;
        this.testGenResults = results;
        this.graph = graph;
        this.isDefaultPattern = isDefaultPattern;
    }

    @Override
    public String toString() {
        int n = 1;
        StringBuilder sb = new StringBuilder();
        sb.append("Test generation results:");
        
        for (TestGenResult testGenResult : testGenResults) {
        	// TODO(YilongL): how to set state id?
            sb.append("\n\nTest case " + n /*+ ", State " + testGenResult.getState().getStateId()*/ + ":");
            
            UnparserFilter t = new UnparserFilter(true, K.color, K.parens, context);
            KRunState.concretize(testGenResult.getGeneratedProgram(), context).accept(t);
            // sb.append("\nProgram:\n" + testGenResult.getGeneratedProgram()); // print abstract syntax form
            sb.append("\nProgram:\n" + t.getResult()); // print concrete syntax form
            sb.append("\nResult:");
            Map<String, Term> substitution = testGenResult.getSubstitution();

            if (isDefaultPattern) {
                UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
                substitution.get("B:Bag").accept(unparser);
                sb.append("\n" + unparser.getResult());
            } else {
                boolean empty = true;

                for (String variable : substitution.keySet()) {
                    UnparserFilter unparser = new UnparserFilter(true, K.color, K.parens, context);
                    sb.append("\n" + variable + " -->");
                    substitution.get(variable).accept(unparser);
                    sb.append("\n" + unparser.getResult());
                    empty = false;
                }
                if (empty) {
                    sb.append("\nEmpty substitution");
                }
            }
            n++;
        }
        
        if (n == 1) {
            sb.append("\nNo test generation results");
        }
        
        return sb.toString();
    }

    public DirectedGraph<KRunState, Transition> getGraph() {
        return graph;
    }

    public List<TestGenResult> getTestGenResults() {
        return testGenResults;
    }
}

