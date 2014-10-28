// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser;

import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Source;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
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
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitTypeCheckVisitor;
import org.kframework.parser.concrete.disambiguate.NormalizeASTTransformer;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PreferDotsFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.TypeInferenceSupremumFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter2;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.parser.generator.DisambiguateRulesFilter;
import org.kframework.parser.generator.ParseConfigsFilter;
import org.kframework.parser.generator.ParseRulesFilter;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.google.inject.Inject;

public class TermLoader {

    private final KExceptionManager kem;

    @Inject
    public TermLoader(KExceptionManager kem) {
        this.kem = kem;
    }

    /**
     * Parses a string representing a file with modules in it. Returns the complete parse tree. Any bubble rule has been parsed and disambiguated.
     *
     * @param content
     *            - the input string.
     * @param source
     *            - only for error reporting purposes. Can be empty string.
     * @param context
     *            - the context for disambiguation purposes.
     * @return A lightweight Definition element which contain all the definition items found in the string.
     */
    public Definition parseString(String content, Source source, Context context) throws ParseFailedException {
        List<DefinitionItem> di = Outer.parse(source, content, context);

        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        def.setItems(di);

        // ------------------------------------- import files in Stratego
        org.kframework.parser.concrete.KParser.ImportTblRule(context.files.resolveKompiled("."));

        // ------------------------------------- parse configs
        JavaClassesFactory.startConstruction(context);
        def = (Definition) new ParseConfigsFilter(context, false, kem).visitNode(def);
        JavaClassesFactory.endConstruction();

        // ----------------------------------- parse rules
        JavaClassesFactory.startConstruction(context);
        def = (Definition) new ParseRulesFilter(context).visitNode(def);
        def = (Definition) new DisambiguateRulesFilter(context, false, kem).visitNode(def);
        def = (Definition) new NormalizeASTTransformer(context, kem).visitNode(def);

        JavaClassesFactory.endConstruction();

        return def;
    }

    public Term parseCmdString(String content, Source source, Sort startSymbol, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }
        String parsed = org.kframework.parser.concrete.KParser.ParseKCmdString(content);
        Document doc = XmlLoader.getXMLDoc(parsed);
        XmlLoader.addSource(doc.getFirstChild(), source);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        org.kframework.kil.ASTNode config = JavaClassesFactory.getTerm((Element) doc.getFirstChild().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        // TODO: reject rewrites
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        //if (checkInclusion)
        //    config = new InclusionFilter(localModule, context).visitNode(config);
        config = new TypeSystemFilter2(startSymbol, context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        config = new CorrectRewritePriorityFilter(context).visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        config = new PriorityFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context, kem).visitNode(config);
        config = new TypeSystemFilter(context).visitNode(config);
        config = new TypeInferenceSupremumFilter(context).visitNode(config);
        // config = new AmbDuplicateFilter(context).visitNode(config);
        // config = new TypeSystemFilter(context).visitNode(config);
        // config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        // config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        config = new PreferAvoidFilter(context).visitNode(config);
        config = new NormalizeASTTransformer(context, kem).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        config = new AmbFilter(context, kem).visitNode(config);

        return (Term) config;
    }

    public ASTNode parsePattern(String pattern, Source source, Sort startSymbol, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }

        String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
        Document doc = XmlLoader.getXMLDoc(parsed);

        XmlLoader.addSource(doc.getFirstChild(), source);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        // TODO: reject rewrites
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        //if (checkInclusion)
        //    config = new InclusionFilter(localModule, context).visitNode(config);
        config = new TypeSystemFilter2(startSymbol, context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        config = new CorrectRewritePriorityFilter(context).visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        config = new PriorityFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context, kem).visitNode(config);
        config = new TypeSystemFilter(context).visitNode(config);
        config = new TypeInferenceSupremumFilter(context).visitNode(config);
        // config = new AmbDuplicateFilter(context).visitNode(config);
        // config = new TypeSystemFilter(context).visitNode(config);
        // config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        // config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        config = new PreferAvoidFilter(context).visitNode(config);
        config = new NormalizeASTTransformer(context, kem).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        config = new AmbFilter(context, kem).visitNode(config);

        return config;
    }

    public ASTNode parsePatternAmbiguous(String pattern, Context context) throws ParseFailedException {
        if (!context.initialized) {
            assert false : "You need to load the definition before you call parsePattern!";
        }

        String parsed = org.kframework.parser.concrete.KParser.ParseKRuleString(pattern);
        Document doc = XmlLoader.getXMLDoc(parsed);

        // XmlLoader.addFilename(doc.getFirstChild(), filename);
        XmlLoader.reportErrors(doc);

        JavaClassesFactory.startConstruction(context);
        ASTNode config = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
        JavaClassesFactory.endConstruction();

        // TODO: don't allow rewrites
        config = new SentenceVariablesFilter(context).visitNode(config);
        config = new CellEndLabelFilter(context).visitNode(config);
        config = new CellTypesFilter(context).visitNode(config);
        // config = new CorrectRewritePriorityFilter().visitNode(config);
        config = new CorrectKSeqFilter(context).visitNode(config);
        config = new CorrectCastPriorityFilter(context).visitNode(config);
        // config = new CheckBinaryPrecedenceFilter().visitNode(config);
        // config = new InclusionFilter(localModule).visitNode(config);
        // config = new VariableTypeInferenceFilter().visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        config = new TypeSystemFilter(context).visitNode(config);
        config = new PreferDotsFilter(context).visitNode(config);
        config = new VariableTypeInferenceFilter(context, kem).visitNode(config);
        // config = new PriorityFilter().visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitTypeCheckVisitor(context), context).visitNode(config);
        config = new TypeInferenceSupremumFilter(context).visitNode(config);
        config = new BestFitFilter(new GetFitnessUnitKCheckVisitor(context), context).visitNode(config);
        // config = new PreferAvoidFilter().visitNode(config);
        config = new NormalizeASTTransformer(context, kem).visitNode(config);
        config = new FlattenListsFilter(context).visitNode(config);
        config = new AmbDuplicateFilter(context).visitNode(config);
        // last resort disambiguation
        // config = new AmbFilter().visitNode(config);
        return config;
    }

}
