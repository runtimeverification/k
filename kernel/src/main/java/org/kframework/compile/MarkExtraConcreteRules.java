package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Rule;
import org.kframework.utils.errorsystem.KEMException;

import javax.annotation.Nullable;
import java.util.HashSet;
import java.util.List;

public class MarkExtraConcreteRules {

    /**
     * Mark with [concrete] rules with labels enumerated in `--concrete-rules`.
     */
    public static Definition mark(Definition def, @Nullable List<String> extraConcreteRuleLabels) {
        if (extraConcreteRuleLabels == null) {
            return def;
        }
        HashSet<String> concreteLabelsSet = new HashSet<>(extraConcreteRuleLabels);
        Definition result = DefinitionTransformer.fromSentenceTransformer((mod, s) -> {
            if (s instanceof Rule) {
                Rule r = (Rule) s;
                String label = r.att().getOption(Att.LABEL()).getOrElse(() -> null);
                if (label != null && extraConcreteRuleLabels.contains(label)) {
                    concreteLabelsSet.remove(label);
                    return Rule.apply(r.body(), r.requires(), r.ensures(), r.att().add(Att.CONCRETE()));
                }
            }
            return s;
        }, "mark extra concrete rules").apply(def);
        if (!concreteLabelsSet.isEmpty()) {
            throw KEMException.criticalError("Unused concrete rule labels: " + concreteLabelsSet);
        }
        return result;
    }
}
