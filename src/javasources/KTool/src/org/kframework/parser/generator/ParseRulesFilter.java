// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Formatter;
import java.util.HashMap;
import java.util.Map;

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
import org.kframework.parser.utils.CachedSentence;
import org.kframework.utils.XmlLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

public class ParseRulesFilter extends ParseForestTransformer {
    final Map<String, CachedSentence> cachedDef;


    public ParseRulesFilter(Context context) {
        super("Parse Rules", context);
        cachedDef = new HashMap<>();
    }

    public ParseRulesFilter(Context context, Map<String, CachedSentence> cachedDef) {
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

            String key = localModule + ss.getContent();
            if (cachedDef.containsKey(key)) {
                String file = ss.getFilename();
                String location = ss.getLocation();
                String msg = "Duplicate rule found in module " + localModule + " at: " + cachedDef.get(key).sentence.getLocation();
                throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, file, location));
            }
            cachedDef.put(key, new CachedSentence(sentence, startLine, startColumn));

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
