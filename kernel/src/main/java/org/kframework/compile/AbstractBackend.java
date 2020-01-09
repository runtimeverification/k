// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.compile;

import com.google.common.collect.Sets;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kprove.KProveOptions;

import java.util.Set;

/**
 * @author Denis Bogdanas
 * Created on 09-Jan-20.
 */
public abstract class AbstractBackend implements Backend {
    /**
     * Will be the default KProveOptions object if not in kprove mode.
     */
    protected final KProveOptions kproveOptions;
    private final Set<String> extraConcreteRuleLabels;

    public AbstractBackend(KProveOptions kproveOptions) {
        this.kproveOptions = kproveOptions;
        this.extraConcreteRuleLabels = Sets.newHashSet(kproveOptions.extraConcreteRuleLabels);
    }

    /**
     * Mark with [concrete] rules with labels enumerated in `--concrete-rules`.
     */
    protected Definition markExtraConcreteRules(Definition d) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(d.mainModule());
        return DefinitionTransformer.fromSentenceTransformer(
                (mod, s) -> markExtraConcreteRules(d, configInfo, s), "mark extra concrete rules").apply(d);
    }

    private Sentence markExtraConcreteRules(Definition d, ConfigurationInfoFromModule configInfo, Sentence s) {
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
