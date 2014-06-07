// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

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
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Formatter;
import java.util.HashMap;
import java.util.Map;

public class CacheLookupFilter extends ParseForestTransformer {
    final Map<String, CachedSentence> cachedDef;
    final Map<String, CachedSentence> kept = new HashMap<>();

    public CacheLookupFilter(Context context, Map<String, CachedSentence> cachedDef) {
        super(CacheLookupFilter.class.getName(), context);
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
            Sentence sentence;

            int startLine = XmlLoader.getLocNumber(ss.getContentLocation(), 0);
            int startColumn = XmlLoader.getLocNumber(ss.getContentLocation(), 1);
            String key = localModule + ss.getContent();

            if (cachedDef.containsKey(key)) {
                // load from cache
                CachedSentence cs = cachedDef.get(key);
                sentence = cs.sentence;
                // fix the location information
                new UpdateLocationVisitor(context, startLine, startColumn,
                                             cs.startLine, cs.startColumn).visitNode(sentence);
                kept.put(key, new CachedSentence(sentence, startLine, startColumn));
                return sentence;
            }
        }
        return ss;
    }

    public Map<String, CachedSentence> getKept() {
        return kept;
    }
}
