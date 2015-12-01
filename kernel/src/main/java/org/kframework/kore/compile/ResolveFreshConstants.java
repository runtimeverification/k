// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.Collections;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.collection.Set;

import java.util.HashSet;
import java.util.Optional;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveFreshConstants {

    private final Definition def;
    private java.util.Set<KVariable> freshVars = new HashSet<>();

    private void reset() {
        freshVars.clear();
    }

    private Rule resolve(Rule rule) {
        reset();
        analyze(rule.body());
        analyze(rule.requires());
        analyze(rule.ensures());
        return Rule(
                rule.body(),
                addSideCondition(rule.requires()),
                rule.ensures(),
                rule.att());
    }

    private void analyze(K term) {
        new VisitKORE() {
            @Override
            public Void apply(KVariable k) {
                if (k.name().startsWith("!")) {
                    freshVars.add(k);
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    private K addSideCondition(K requires) {
        Optional<KApply> sideCondition = freshVars.stream().map(k -> {
            Optional<String> s = k.att().<String>getOptional(Attribute.SORT_KEY);
            if (!s.isPresent()) {
                throw KEMException.compilerError("Fresh constant used without a declared sort.", k);
            }
            return KApply(KLabel("#match"), k, KApply(KLabel("#fresh"), KToken(StringUtil.enquoteKString(s.get()), Sorts.String())));
        }).reduce(BooleanUtils::and);
        if (!sideCondition.isPresent()) {
            return requires;
        } else if (requires.equals(BooleanUtils.TRUE) && sideCondition.isPresent()) {
            return sideCondition.get();
        } else {
            // we order the lookup after the requires clause so that the fresh constant
            // matching side condition occurs last. This is necessary in order to
            // ensure that fresh constants in rule RHSs are consecutive
            return BooleanUtils.and(requires, sideCondition.get());
        }
    }

    private Context resolve(Context context) {
        reset();
        analyze(context.body());
        analyze(context.requires());
        return new Context(
                context.body(),
                addSideCondition(context.requires()),
                context.att());
    }

    private Sentence resolve(Sentence s) {
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
        Set<Sentence> sentences = map(this::resolve, m.localSentences());
        if (sentences.equals(m.localSentences())) {
            return m;
        }
        return Module(m.name(), add(def.getModule("K-REFLECTION").get(), m.imports()), sentences, m.att());
    }
}

