// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.Sentence;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CellTypesFilter;
import org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.CorrectRewritePriorityFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.InclusionFilter;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;

public class DisambiguateRulesFilter extends ParseForestTransformer {
    boolean checkInclusion = true;

    public DisambiguateRulesFilter(Context context, boolean checkInclusion) {
        super(DisambiguateRulesFilter.class.getName(), context);
        this.checkInclusion = checkInclusion;
    }

    String localModule = null;

    @Override
    public ASTNode visit(Module m, Void _) throws ParseFailedException {
        localModule = m.getName();
        return super.visit(m, _);
    }

    public ASTNode visit(Sentence ss, Void _) throws ParseFailedException {
        ASTNode config = ss;
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        if (checkInclusion)
            config = new InclusionFilter(localModule, context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        config = new CorrectRewritePriorityFilter(context).visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        config = new PriorityFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context).visitNode(config);
        // config = new AmbDuplicateFilter(context).visitNode(config);
        // config = new TypeSystemFilter(context).visitNode(config);
        // config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        // config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        config = new PreferAvoidFilter(context).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        config = new AmbFilter(context).visitNode(config);
        return config;
    }

    public boolean isCheckInclusion() {
        return checkInclusion;
    }

    public void setCheckInclusion(boolean checkInclusion) {
        this.checkInclusion = checkInclusion;
    }
}
