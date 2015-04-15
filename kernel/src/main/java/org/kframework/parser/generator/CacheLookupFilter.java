// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Module;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringSentence;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.parser.utils.CachedSentence;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
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
    public ASTNode visit(Module m, Void _void) throws ParseFailedException {
        localModule = m.getName();
        return super.visit(m, _void);
    }

    public ASTNode visit(StringSentence ss, Void _void) throws ParseFailedException {
        if (ss.getType().equals(Constants.RULE) || ss.getType().equals(Constants.CONTEXT)) {
            Sentence sentence;

            String key = localModule + ss.getContent();

            if (cachedDef.containsKey(key)) {
                // load from cache
                CachedSentence cs = cachedDef.get(key);
                sentence = cs.sentence;
                // take the attributes from the current StringSentence, since they are being parsed in the outer parser.
                sentence.setAttributes(ss.getAttributes());
                if (kept.containsKey(key)) {
                    Source source = ss.getSource();
                    Location location = ss.getLocation();
                    String msg = "Duplicate rule found in module " + localModule + " at: " + cachedDef.get(key).sentence.getLocation();
                    throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, source, location));
                }

                // fix the location information
                new UpdateLocationVisitor(ss.getContentStartLine(), ss.getContentStartColumn(),
                                             cs.startLine, cs.startColumn).visitNode(sentence);
                kept.put(key, new CachedSentence(sentence, ss.getContentStartLine(), ss.getContentStartColumn()));
                return sentence;
            }
        }
        return ss;
    }

    public Map<String, CachedSentence> getKept() {
        return kept;
    }
}
