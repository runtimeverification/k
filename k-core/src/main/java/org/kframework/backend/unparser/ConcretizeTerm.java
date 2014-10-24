// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.compile.transformers.DataStructure2Cell;
import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.krun.ConcretizeSyntax;
import org.kframework.krun.FlattenDisambiguationFilter;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.SubstitutionFilter;
import org.kframework.krun.api.SearchResult;
import org.kframework.parser.TermLoader;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;

import com.google.inject.Inject;

public class ConcretizeTerm {

    private final TermLoader loader;
    private final KRunOptions krunOptions;

    @Inject
    public ConcretizeTerm(TermLoader loader, KRunOptions krunOptions) {
        this.loader = loader;
        this.krunOptions = krunOptions;
    }

    public Map<String, Term> concretizeSubstitution(Context context, SearchResult result) {
        Map<String, Term> substitution = new HashMap<>();
        for (Variable var : result.getCompilationInfo().getVars()) {
            Term rawValue;

            rawValue = result.getRawSubstitution().get(var.getName());

            substitution.put(var.toString(), concretize(context, rawValue));
        }
        return substitution;
    }

    public Term concretize(Context context, Term result) {
        result = (Term) new DataStructure2Cell(context).visitNode(result);
        result = (Term) new ConcretizeSyntax(context).visitNode(result);
        result = (Term) new TypeInferenceSupremumFilter(context).visitNode(result);
        result = (Term) new FlattenDisambiguationFilter(context).visitNode(result);
        result = (Term) new ConcretizeSyntax.RemoveEmptyLists(context).visitNode(result);
        result = (Term) new AddBracketsFilter(context).visitNode(result);
        if (krunOptions.output == OutputModes.SMART) {
            /* collect existing free variables in the result */
            final Set<Variable> existingFreeVariables = new HashSet<Variable>();
            BasicVisitor variableCollector = new BasicVisitor(context) {
                @Override
                public Void visit(Variable var, Void _void) {
                    existingFreeVariables.add(var);
                    return null;
                }
            };
            variableCollector.visitNode(result);

            /* add brackets */
            AddBracketsFilter2 filter = new AddBracketsFilter2(context, loader);
            result = (Term) filter.visitNode(result);

            /* initialize the substitution map of the filter using existing free variables */
            Map<String, Term> subst = new HashMap<String, Term>(filter.substitution);
            for (Variable var : existingFreeVariables) {
                subst.put(var.getName(), var);
            }
            while (true) {
                Term newResult = (Term) new SubstitutionFilter(subst, context).visitNode(result);
                if (newResult.equals(result)) {
                    break;
                }
                result = newResult;
            }
        }
        if (result.getClass() == Cell.class) {
            Cell generatedTop = (Cell) result;
            if (generatedTop.getLabel().equals("generatedTop")) {
                result = generatedTop.getContents();
            }
        }

        return result;
    }
}
