// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class ResolveAnonVar {

    public static KVariable ANON_VAR = KVariable("_");
    public static KVariable FRESH_ANON_VAR = KVariable("?_");
    public static KVariable FRESH_ANON_CONSTANT = KVariable("!_");

    public static boolean isAnonVar(KVariable var) {
        return var.equals(ANON_VAR) || var.equals(FRESH_ANON_VAR) || var.equals(FRESH_ANON_CONSTANT);
    }

    private Set<KVariable> vars = new HashSet<>();

    void resetVars() {
        vars.clear();
        counter = 0;
    }

    private Rule resolve(Rule rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        return new Rule(
                transform(rule.body()),
                transform(rule.requires()),
                transform(rule.ensures()),
                rule.att());
    }

    private Context resolve(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    private ContextAlias resolve(ContextAlias context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        return new ContextAlias(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    public K resolveK(K k) {
        resetVars();;
        gatherVars(k);
        return transform(k);
    }

    public synchronized Sentence resolve(Sentence s) {
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else if (s instanceof ContextAlias) {
            return resolve((ContextAlias) s);
        } else {
            return s;
        }
    }

    void gatherVars(K term) {
        new VisitK() {
            @Override
            public void apply(KVariable v) {
                vars.add(v);
                super.apply(v);
            }
        }.apply(term);
    }

    K transform(K term) {
        return new TransformK() {
            @Override
            public K apply(KVariable k) {
                if (ANON_VAR.equals(k)) {
                    return newDotVariable("");
                }
                if (FRESH_ANON_VAR.equals(k)) {
                    return newDotVariable("?");
                }
                if (FRESH_ANON_CONSTANT.equals(k)) {
                    return newDotVariable("!");
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    private int counter = 0;
    KVariable newDotVariable(String prefix) {
        KVariable newLabel;
        Att att = Att().add("anonymous");
        if (prefix.equals("?")) {
            att = att.add("fresh");
        }
        do {
            newLabel = KVariable(prefix + "_" + (counter++), att);
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

}
