package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.indexing.BottomIndex;
import org.kframework.backend.java.indexing.FreezerIndex;
import org.kframework.backend.java.indexing.Index;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.indexing.KLabelIndex;
import org.kframework.backend.java.indexing.TokenIndex;
import org.kframework.backend.java.indexing.TopIndex;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;
import com.google.common.collect.ImmutableSet;


/**
 *
 *
 * @author AndreiS
 */
public class SymbolicRewriter {

    private final Context context;
    private final Definition definition;
	private final SymbolicMatcher matcher;
    private final Stopwatch stopwatch = new Stopwatch();
    public final Stopwatch ruleStopwatch = new Stopwatch();
    private final Map<IndexingPair, Set<Rule>> ruleTable;
    private IndexingPair tableIndex;

	public SymbolicRewriter(Definition definition, Context context) {
        this.definition = definition;
        this.context = context;
		matcher = new SymbolicMatcher(context);

        ruleTable = new HashMap<IndexingPair, Set<Rule>>();

        Set<Index> indices = new HashSet<Index>();
        indices.add(TopIndex.TOP);
        indices.add(BottomIndex.BOTTOM);
        for (KLabelConstant kLabel : definition.kLabels()) {
            indices.add(new KLabelIndex(kLabel));
        }
        for (KLabelConstant frozenKLabel : definition.frozenKLabels()) {
            indices.add(new FreezerIndex(frozenKLabel, -1));
            for (int i = 0; i < frozenKLabel.productions().get(0).getArity(); ++i) {
                indices.add(new FreezerIndex(frozenKLabel, i));
            }
        }
        for (String sort : Definition.TOKEN_SORTS) {
            indices.add(new TokenIndex(sort));
        }

        for (Index first : indices) {
            for (Index second : indices) {
                IndexingPair pair = new IndexingPair(first, second);

                ImmutableSet.Builder<Rule> builder = ImmutableSet.builder();
                for (Rule rule : definition.rules()) {
                    if (pair.isUnifiable(rule.indexingPair())) {
                        builder.add(rule);
                    }
                }

                ImmutableSet<Rule> rules = builder.build();
                if (!rules.isEmpty()) {
                    ruleTable.put(pair, rules);
                }
            }
        }
	}

    public long elapsed() {
        return stopwatch.elapsed(TimeUnit.MILLISECONDS);
    }

    public Term rewriteN(Term term, int n) {
        stopwatch.start();
        for (int i = 0; i < n; ++i) {
            Term resultTerm = rewrite(term);
            if (resultTerm != null) {
                term = resultTerm;
            } else {
                return term;
            }
        }
        stopwatch.stop();

        return term;
    }

    public Term rewriteStar(Term term) {
        stopwatch.start();
        while (true) {
            Term resultTerm = rewrite(term);
            if (resultTerm != null) {
                term = resultTerm;
            } else {
                break;
            }
        }
        stopwatch.stop();

        return term;
    }

    private void init(Term term) {
        Cell generatedTopCell = (Cell) term;
        Cell TCell = ((CellCollection) generatedTopCell.getContent()).get("T");
        Cell kCell = ((CellCollection) TCell.getContent()).get("k");
        Term content = kCell.getContent();
        tableIndex = IndexingPair.getIndexingPair(content);
    }

    private Term rewrite(Term term) {
        init(term);
        if (ruleTable.get(tableIndex) == null) {
            return null;
        }
        Set<Rule> rules = ruleTable.get(tableIndex);

        for (Rule rule : rules) {
            ruleStopwatch.reset();
            ruleStopwatch.start();
            if (matcher.isMatching(term, rule.leftHandSide())) {
                SymbolicConstraint constraint = matcher.constraint();
                constraint.addAll(rule.lookups());
                //constraint.addAll(rule.condition());
                constraint.add(rule.condition(), BoolToken.TRUE);

                if (constraint.isFalse()) {
                    continue;
                }

                /* rename rule variables in the constraints */
                Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

                Term result = rule.rightHandSide();
                /* rename rule variables in the rule RHS */
                result = result.substitute(freshSubstitution, context);
                /* apply the constraints substitution on the rule RHS */
                result = result.substitute(constraint.substitution(), context);
                /* evaluate pending functions in the rule RHS */
                result = result.evaluate(context);


                System.err.println("rule \n\t" + rule);
                System.err.println("result constraint\n\t" + constraint);
                System.err.println("result term\n\t" + result);
                System.err.println("============================================================");


                /* return first match */
                ruleStopwatch.stop();
                System.err.println("### " + ruleStopwatch);
                return result;
            }
            ruleStopwatch.stop();
            System.err.println(ruleStopwatch);
        }

        return null;
    }

}
