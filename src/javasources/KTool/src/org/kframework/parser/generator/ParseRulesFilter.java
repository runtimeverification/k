// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Formatter;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
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
import org.kframework.utils.XmlLoader;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class ParseRulesFilter extends ParseForestTransformer {
    boolean checkInclusion = true;

    public ParseRulesFilter(Context context, boolean checkInclusion) {
        super("Parse Rules", context);
        this.checkInclusion = checkInclusion;
    }

    public ParseRulesFilter(Context context) {
        super("Parse Rules", context);
    }

    String localModule = null;

    @Override
    public ASTNode visit(Module m, Void _) throws ParseFailedException {
        localModule = m.getName();
        return super.visit(m, _);
    }

    public ASTNode visit(StringSentence ss, Void _) throws ParseFailedException {
        if (ss.getType().equals(Constants.RULE) || ss.getType().equals(Constants.CONTEXT)) {
            long startTime = System.currentTimeMillis();
            try {
                ASTNode config;

                String parsed = null;
                if (ss.containsAttribute("kore")) {

                    long koreStartTime = System.currentTimeMillis();
                    parsed = org.kframework.parser.concrete.KParser.ParseKoreString(ss.getContent());
                    if (globalOptions.verbose)
                        System.out.println("Parsing with Kore: " + ss.getFilename() + ":" + ss.getLocation() + " - " + (System.currentTimeMillis() - koreStartTime));
                } else
                    parsed = org.kframework.parser.concrete.KParser.ParseKConfigString(ss.getContent());
                Document doc = XmlLoader.getXMLDoc(parsed);

                // replace the old xml node with the newly parsed sentence
                Node xmlTerm = doc.getFirstChild().getFirstChild().getNextSibling();
                XmlLoader.updateLocation(xmlTerm, XmlLoader.getLocNumber(ss.getContentLocation(), 0), XmlLoader.getLocNumber(ss.getContentLocation(), 1));
                XmlLoader.addFilename(xmlTerm, ss.getFilename());
                XmlLoader.reportErrors(doc, ss.getType());

                if (ss.getType().equals(Constants.CONTEXT))
                    config = new org.kframework.kil.Context((Sentence) JavaClassesFactory.getTerm((Element) xmlTerm));
                else if (ss.getType().equals(Constants.RULE))
                    config = new Rule((Sentence) JavaClassesFactory.getTerm((Element) xmlTerm));
                else { // should not reach here
                    config = null;
                    assert false : "Only context and rules have been implemented.";
                }
                Sentence st = (Sentence) config;
                assert st.getLabel().equals(""); // labels should have been parsed in Basic Parsing
                st.setLabel(ss.getLabel());
                //assert st.getAttributes() == null || st.getAttributes().isEmpty(); // attributes should have been parsed in Basic Parsing
                st.setAttributes(ss.getAttributes());

                // disambiguate rules
                if (config.getFilename().endsWith("test.k")) {
                    // this is just for testing. I put a breakpoint on the next line so I can get faster to the rule that I'm interested in
                    int a = 1;
                    a = a + 1;
                }

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

                if (globalOptions.debug) {
                    try (Formatter f = new Formatter(new FileWriter(context.dotk.getAbsolutePath() + "/timing.log", true))) {
                        f.format("Parsing rule: Time: %6d Location: %s:%s\n", (System.currentTimeMillis() - startTime), ss.getFilename(), ss.getLocation());
                    } catch (IOException e) {
                        e.printStackTrace();
                    }
                }
                return config;
            } catch (ParseFailedException te) {
                te.printStackTrace();
            }
        }
        return ss;
    }

    public boolean isCheckInclusion() {
        return checkInclusion;
    }

    public void setCheckInclusion(boolean checkInclusion) {
        this.checkInclusion = checkInclusion;
    }
}
