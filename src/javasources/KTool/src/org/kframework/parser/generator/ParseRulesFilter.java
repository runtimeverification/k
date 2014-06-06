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
import org.kframework.parser.utils.CacheContainer.CachedSentence;
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
            Sentence sentence;

            int startLine = XmlLoader.getLocNumber(ss.getContentLocation(), 0);
            int startColumn = XmlLoader.getLocNumber(ss.getContentLocation(), 1);

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
                XmlLoader.updateLocation(xmlTerm, startLine, startColumn);
                XmlLoader.addFilename(xmlTerm, ss.getFilename());
                XmlLoader.reportErrors(doc, ss.getType());

                Sentence st = (Sentence) JavaClassesFactory.getTerm((Element) xmlTerm);
                assert st.getLabel().equals(""); // labels should have been parsed in Basic Parsing
                st.setLabel(ss.getLabel());
                st.setAttributes(ss.getAttributes());

                if (Constants.CONTEXT.equals(ss.getType()))
                    sentence = new org.kframework.kil.Context(st);
                else if (Constants.RULE.equals(ss.getType()))
                    sentence = new Rule(st);
                else { // should not reach here
                    sentence = null;
                    assert false : "Only context and rules have been implemented. Found: " + ss.getType();
                }

                cachedDef.parsedSentences++;
            } else {
                // load from cache
                CachedSentence cs = cachedDef.sentences.get(localModule + ss.getContent());
                sentence = cs.sentence;
                // fix the location information
                new UpdateLocationVisitor(context, startLine, startColumn,
                                             cs.startLine, cs.startColumn).visitNode(sentence);
            }

            cachedDef.sentences.put(localModule + ss.getContent(), cachedDef.new CachedSentence(sentence, startLine, startColumn));
            cachedDef.totalSentences++;

            if (globalOptions.debug) {
                try (Formatter f = new Formatter(new FileWriter(context.dotk.getAbsolutePath() + "/timing.log", true))) {
                    f.format("Parsing rule: Time: %6d Location: %s:%s\n", (System.currentTimeMillis() - startTime), ss.getFilename(), ss.getLocation());
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
            return sentence;
        }
        return ss;
    }
}
