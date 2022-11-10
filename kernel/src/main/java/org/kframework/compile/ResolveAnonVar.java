// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.HashSet;
import java.util.Set;

import static org.kframework.kore.KORE.*;

public class ResolveAnonVar {

    public static KVariable ANON_VAR = KVariable("_");
    public static KVariable FRESH_ANON_VAR = KVariable("?_");
    public static KVariable FRESH_ANON_CONSTANT = KVariable("!_");
    public static KVariable FRESH_LIST_VAR = KVariable("@_");

    public static boolean isAnonVar(KVariable var) {
        return var.equals(ANON_VAR) || var.equals(FRESH_ANON_VAR) || var.equals(FRESH_ANON_CONSTANT) || var.equals(FRESH_LIST_VAR);
    }

    public static boolean isAnonVarOrNamedAnonVar(KVariable var) {
        return var.name().startsWith(ANON_VAR.name())
                || var.name().startsWith(FRESH_ANON_VAR.name())
                || var.name().startsWith(FRESH_ANON_CONSTANT.name())
                || var.name().startsWith(FRESH_LIST_VAR.name());
    }


    private Set<KVariable> vars = new HashSet<>();

    void resetVars() {
        vars.clear();
        counter = 0;
    }

    private RuleOrClaim resolve(RuleOrClaim rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        return rule.newInstance(
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
        if (s instanceof RuleOrClaim) {
            return resolve((RuleOrClaim) s);
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
                if (FRESH_LIST_VAR.equals(k)) {
                    return newDotVariable("@");
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
            newLabel = KVariable(prefix + "_Gen" + (counter++), att);
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

}
