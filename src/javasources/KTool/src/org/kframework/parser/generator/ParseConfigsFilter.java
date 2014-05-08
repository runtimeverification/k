// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Module;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.loader.CollectStartSymbolPgmVisitor;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbDuplicateFilter;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.BestFitFilter;
import org.kframework.parser.concrete.disambiguate.CellEndLabelFilter;
import org.kframework.parser.concrete.disambiguate.CorrectCastPriorityFilter;
import org.kframework.parser.concrete.disambiguate.CorrectConstantsTransformer;
import org.kframework.parser.concrete.disambiguate.CorrectKSeqFilter;
import org.kframework.parser.concrete.disambiguate.FlattenListsFilter;
import org.kframework.parser.concrete.disambiguate.GetFitnessUnitKCheckVisitor;
import org.kframework.parser.concrete.disambiguate.InclusionFilter;
import org.kframework.parser.concrete.disambiguate.MergeAmbFilter;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.parser.concrete.disambiguate.SentenceVariablesFilter;
import org.kframework.parser.concrete.disambiguate.VariableTypeInferenceFilter;
import org.kframework.parser.utils.ReportErrorsVisitor;
import org.kframework.parser.utils.Sglr;
import org.kframework.utils.StringUtil;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class ParseConfigsFilter extends BasicTransformer {
    public ParseConfigsFilter(Context context) {
        super("Parse Configurations", context);
    }

    public ParseConfigsFilter(Context context, boolean checkInclusion) {
        super("Parse Configurations", context);
        this.checkInclusion = checkInclusion;
    }

    boolean checkInclusion = true;
    String localModule = null;

    @Override
    public ASTNode visit(Module m, Void _) throws TransformerException {
        localModule = m.getName();
        ASTNode rez = super.visit(m, _);
        new CollectStartSymbolPgmVisitor(context).visitNode(rez);
        return rez;
    }

    public ASTNode visit(StringSentence ss, Void _) throws TransformerException {
        if (ss.getType().equals(Constants.CONFIG)) {
            try {
                ASTNode config = null;
                String parsed = null;
                if (ss.containsAttribute("kore")) {
                    long startTime = System.currentTimeMillis();
                    parsed = org.kframework.parser.concrete.KParser.ParseKoreString(ss.getContent());
                    if (globalOptions.verbose)
                        System.out.println("Parsing with Kore: " + ss.getFilename() + ":" + ss.getLocation() + " - " + (System.currentTimeMillis() - startTime));
                } else
                    parsed = org.kframework.parser.concrete.KParser.ParseKConfigString(ss.getContent());
                Document doc = XmlLoader.getXMLDoc(parsed);

                // replace the old xml node with the newly parsed sentence
                Node xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
                XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(ss.getContentLocation(), 0), XmlLoader.getLocNumber(ss.getContentLocation(), 1));
                XmlLoader.addFilename(xmlTerm, ss.getFilename());
                XmlLoader.reportErrors(doc, ss.getType());

                Sentence st = (Sentence) JavaClassesFactory.getTerm((Element) xmlTerm);
                config = new Configuration(st);
                assert st.getLabel().equals(""); // labels should have been parsed in Basic Parsing
                st.setLabel(ss.getLabel());
                //assert st.getAttributes() == null || st.getAttributes().isEmpty(); // attributes should have been parsed in Basic Parsing
                st.setAttributes(ss.getAttributes());

                // disambiguate configs
                config = new SentenceVariablesFilter(context).visitNode(config);
                config = new CellEndLabelFilter(context).visitNode(config);
                if (checkInclusion)
                    config = new InclusionFilter(localModule, context).visitNode(config);
                // config = new CellTypesFilter().visitNode(config); not the case on configs
                // config = new CorrectRewritePriorityFilter().visitNode(config);
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
            } catch (TransformerException te) {
                te.printStackTrace();
            }
        }
        return ss;
    }
}
