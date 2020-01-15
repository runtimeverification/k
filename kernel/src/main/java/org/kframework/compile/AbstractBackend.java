// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import scala.Function1;

import javax.annotation.Nullable;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * @author Denis Bogdanas
 * Created on 09-Jan-20.
 */
public abstract class AbstractBackend implements Backend {

    @Override
    public Function<Definition, Definition> proofDefinitionNonCachedSteps(
            @Nullable List<String> extraConcreteRuleLabels) {
        Function1<Definition, Definition> markExtraConcrete =
                def -> markExtraConcreteRules(def, extraConcreteRuleLabels);
        return markExtraConcrete::apply;
    }

    protected Definition markExtraConcreteRules(Definition def, @Nullable List<String> extraConcreteRuleLabels) {
        if (extraConcreteRuleLabels == null) {
            return def;
        }
        HashSet<String> concreteLabelsSet = new HashSet<>(extraConcreteRuleLabels);
        return DefinitionTransformer.fromSentenceTransformer(
                (mod, s) -> markExtraConcreteRules(s, concreteLabelsSet), "mark extra concrete rules")
                .apply(def);
    }

    /**
     * Mark with [concrete] rules with labels enumerated in `--concrete-rules`.
     */
    private Sentence markExtraConcreteRules(Sentence s, Set<String> extraConcreteRuleLabels) {
        if (s instanceof org.kframework.definition.Rule) {
            org.kframework.definition.Rule r = (org.kframework.definition.Rule) s;
            String label = r.att().getOption(Attribute.LABEL_KEY).getOrElse(() -> null);
            if (label != null && extraConcreteRuleLabels.contains(label)) {
                return Rule.apply(r.body(), r.requires(), r.ensures(), r.att().add(Attribute.CONCRETE_KEY));
            }
        }
        return s;
    }
}
