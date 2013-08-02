package org.kframework.krun.api;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;

import java.util.List;
import java.util.Map;

/**
 * Created with IntelliJ IDEA.
 * User: owolabi
 * Date: 8/2/13
 * Time: 2:05 AM
 * To change this template use File | Settings | File Templates.
 */
public class GeneratorResults{
    private List<GeneratorResult> solutions;
    private DirectedGraph<KRunState, Transition> graph;
    private boolean isDefaultPattern;

    protected Context context;

    public GeneratorResults(List<GeneratorResult> solutions, DirectedGraph<KRunState, Transition> graph, boolean isDefaultPattern, Context context) {
        this.context = context;
        this.solutions = solutions;
        this.graph = graph;
        this.isDefaultPattern = isDefaultPattern;
    }

    @Override
    public String toString() {
        int i = 1;
        StringBuilder sb = new StringBuilder();
        sb.append("Generator results:");
        for (GeneratorResult solution : solutions) {
//            Term search = solution.getState().getRawResult();
            sb.append("\n\nSolution " + i + ", State " + solution.getState().getStateId() + ":");

            sb.append("\nProgram:\n"+solution.getGeneratedProgram());

            Map<String, Term> substitution = solution.getSubstitution();

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
            i++;
        }
        if (i == 1) {
            sb.append("\nNo search results");
        }
        return sb.toString();
    }

    public DirectedGraph<KRunState, Transition> getGraph() {
        return graph;
    }

    public List<GeneratorResult> getSolutions() {
        return solutions;
    }
}

