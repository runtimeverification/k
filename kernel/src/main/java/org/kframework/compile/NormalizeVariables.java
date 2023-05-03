// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Normalizes variable names in terms and sentences according to alpha equivalence.
 * Variables that have previously been normalized are not normalized on succeeding passes,
 * allowing the user to fine-tune the normalization such that arbitrary subterms can share
 * a common prefix.
 */
public class NormalizeVariables {

    private int counter = 0;
    private Map<KVariable, String> vars = new HashMap<>();
    private KVariable normalize(KVariable var) {
        if (var.att().contains(Att.DENORMAL()))
            return var;
        if (!vars.containsKey(var)) {
            vars.put(var, "_" + counter++);
        }
        return KVariable(vars.get(var), var.att().add(Att.DENORMAL(), var.name()));
    }

    /**
     * Applies the normalization existing in a particular set of normalized terms to a denormal term
     * @param denormal The term to be normalized. Only variables which exist in the specified
     *                 {@code normals} are normalized.
     * @param normals A list of terms that have previously been normalized using this class, or which
     *               have been constructed manually with all variables given the "denormal"
     *               attribute specifying their denormal name. The term to be normalized
     *               will be normalized according to the same normalization as these terms.
     * @return The normalized version of {@code denormal}, in which each variable present in
     * the denormal version of the specified {@code normals} is replaced with its normalized
     * name.
     */
    public K applyNormalization(K denormal, K... normals) {
        Map<KVariable, String> normalization = inferNormalizationFromTerm(normals);
        return new TransformK() {
            @Override
            public K apply(KVariable k) {
                if (normalization.containsKey(k)) {
                    return KVariable(normalization.get(k), k.att().add(Att.DENORMAL(), k.name()));
                }
                return super.apply(k);
            }
        }.apply(denormal);
    }

    private Map<KVariable, String> inferNormalizationFromTerm(K[] normals) {
        Map<KVariable, String> normalization = new HashMap<>();
        for (K normal : normals) {
            new VisitK() {
                @Override
                public void apply(KVariable k) {
                    if (k.att().contains(Att.DENORMAL())) {
                        normalization.put(KVariable(k.att().get(Att.DENORMAL())), k.name());
                    }
                }
            }.apply(normal);
        }
        return normalization;
    }

    public Rule applyNormalization(Rule denormal, K... normals) {
        return Rule(
                applyNormalization(denormal.body(), normals),
                applyNormalization(denormal.requires(), normals),
                applyNormalization(denormal.ensures(), normals),
                denormal.att());
    }

    public K normalize(K term, K... normals) {
        resetVars(Stream.concat(Stream.of(term), Arrays.stream(normals)).toArray(K[]::new));
        return transform(term);
    }

    public K transform(K term) {
        return new TransformK() {
            @Override
            public K apply(KVariable k) {
                return normalize(k);
            }
        }.apply(term);
    }

    private void resetVars(K... normals) {
        vars = inferNormalizationFromTerm(normals);
        counter = vars.size();
    }

    public Rule normalize(Rule rule) {
        resetVars(rule.body(), rule.requires(), rule.ensures());
        return Rule(
                transform(rule.body()),
                transform(rule.requires()),
                transform(rule.ensures()),
                rule.att());
    }

    private Context normalize(Context context) {
        resetVars(context.body(), context.requires());
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    public Sentence normalize(Sentence s) {
        if (s instanceof Rule) {
            return normalize((Rule) s);
        } else if (s instanceof Context) {
            return normalize((Context) s);
        } else {
            return s;
        }
    }
}
