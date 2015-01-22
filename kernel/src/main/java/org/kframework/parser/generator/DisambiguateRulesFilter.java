// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Sentence;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
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
import org.kframework.parser.concrete.disambiguate.PreferDotsFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;

public class DisambiguateRulesFilter extends ParseForestTransformer {
    boolean checkInclusion = true;

    private final KExceptionManager kem;

    public DisambiguateRulesFilter(Context context, boolean checkInclusion, KExceptionManager kem) {
        super(DisambiguateRulesFilter.class.getName(), context);
        this.checkInclusion = checkInclusion;
        this.kem = kem;
    }

    public ASTNode visit(Sentence ss, Void _void) throws ParseFailedException {
        assert (getCurrentModule() != null);
        ASTNode config = ss;
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        if (checkInclusion)
            config = new InclusionFilter(context, getCurrentDefinition(), getCurrentModule())
                    .visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        config = new CorrectRewritePriorityFilter(context).visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        config = new PriorityFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context, kem).visitNode(config);
        // config = new AmbDuplicateFilter(context).visitNode(config);
        // config = new TypeSystemFilter(context).visitNode(config);
        // config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        // config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        config = new PreferAvoidFilter(context).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        config = new AmbFilter(context, kem).visitNode(config);
        return config;
    }
}
