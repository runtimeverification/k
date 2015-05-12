package org.kframework.kore.compile;

import org.kframework.Collections;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.immutable.Set;

import java.util.Optional;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveFreshConstants {

    private final Definition def;

    private Rule resolve(Rule rule) {
        return Rule(
                transform(rule.body()),
                transform(rule.requires()),
                transform(rule.ensures()),
                rule.att());
    }

    private K transform(K term) {
        return new TransformKORE() {
            @Override
            public K apply(KVariable k) {
                if (k.name().startsWith("!")) {
                    Optional<String> s = k.att().<String>getOptional(Attribute.SORT_KEY);
                    if (!s.isPresent()) {
                        throw KEMException.compilerError("Fresh constant used without a declared sort.", k);
                    }
                    return KApply(KLabel("#fresh"), KToken(StringUtil.enquoteKString(s.get()), Sorts.String()));
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    private Context resolve(Context context) {
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    private synchronized Sentence resolve(Sentence s) {
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else {
            return s;
        }
    }

    public ResolveFreshConstants(Definition def) {
        this.def = def;
    }

    public Module resolve(Module m) {
        Set<Sentence> sentences = stream(m.localSentences()).map(this::resolve).collect(Collections.toSet());
        if (sentences.equals(m.localSentences())) {
            return m;
        }
        return Module(m.name(), Stream.concat(Stream.of(def.getModule("K-REFLECTION").get()), stream(m.imports())).collect(Collections.toSet()), sentences, m.att());
    }
}
