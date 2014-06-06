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
import org.kframework.parser.utils.CacheContainer;
import org.kframework.utils.XmlLoader;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class ParseRulesFilter extends ParseForestTransformer {
    final CacheContainer cachedDef;

    public ParseRulesFilter(Context context, boolean checkInclusion) {
        super("Parse Rules", context);
        cachedDef = null;
    }

    public ParseRulesFilter(Context context, CacheContainer cachedDef) {
        super("Parse Rules", context);
        this.cachedDef = cachedDef;
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
            ASTNode config;

            if (!(cachedDef.sentences.containsKey(localModule + ss.getContent()))) {
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

                // store into cache
                // TODO: see how to report ambiguities next time when loading from cache
                // because it uses the same objects, the filters will disambiguate before serialization
                cachedDef.sentences.put(localModule + ss.getContent(), (Sentence) config);
                cachedDef.parsedSentences++;
            } else {
                // load from cache
                config = cachedDef.sentences.get(localModule + ss.getContent());
                //System.out.println(ss.getLocation() + " " + config.getLocation());
                // TODO: fix the location information
            }

            if (globalOptions.debug) {
                try (Formatter f = new Formatter(new FileWriter(context.dotk.getAbsolutePath() + "/timing.log", true))) {
                    f.format("Parsing rule: Time: %6d Location: %s:%s\n", (System.currentTimeMillis() - startTime), ss.getFilename(), ss.getLocation());
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
            cachedDef.totalSentences++;
            return config;
        }
        return ss;
    }
}
