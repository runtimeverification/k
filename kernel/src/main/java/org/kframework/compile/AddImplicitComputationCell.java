// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;

import java.util.List;
import java.util.stream.Stream;

/**
 *  If a SemanticSentence (Rule or Context) has a body that is not wrapped in any cell,
 *  wrap it in a {@code <k>} cell
 */
public class AddImplicitComputationCell {

    public static Definition transformDefinition(Definition input) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
        LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
        return DefinitionTransformer.fromSentenceTransformer(
                new AddImplicitComputationCell(configInfo, labelInfo)::apply,
                "concretizing configuration").apply(input);
    }

    public static Module transformModule(Module mod) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(mod);
        LabelInfo labelInfo = new LabelInfoFromModule(mod);
        return ModuleTransformer.fromSentenceTransformer(
                new AddImplicitComputationCell(configInfo, labelInfo)::apply,
                "concretizing configuration").apply(mod);
    }

    private final ConfigurationInfo cfg;
    private final LabelInfo labelInfo;

    public AddImplicitComputationCell(ConfigurationInfo cfg, LabelInfo labelInfo) {
        this.cfg = cfg;
        this.labelInfo = labelInfo;
    }

    public Sentence apply(Module m, Sentence s) {
        if (skipSentence(s)) {
            return s;
        }

        if (s instanceof RuleOrClaim) {
            RuleOrClaim rule = (RuleOrClaim) s;
            return rule.newInstance(apply(rule.body(), m), rule.requires(), rule.ensures(), rule.att());
        } else if (s instanceof Context) {
            Context context = (Context) s;
            return new Context(apply(context.body(), m), context.requires(), context.att());
        } else {
            return s;
        }
    }

    private boolean skipSentence(Sentence s) {
        return ExpandMacros.isMacro(s)
                || s.att().contains(Att.ANYWHERE())
                || s.att().contains(Att.SIMPLIFICATION())
                || s.att().contains(Att.KORE());
    }

    private K apply(K term, Module m) {
        if (m.isFunction(term)) return term;

        List<K> items = IncompleteCellUtils.flattenCells(term);
        if (items.size() != 1) {
            return term;
        }
        K item = items.get(0);
        if (isCell(item)) {
            return term;
        } else if (item instanceof KRewrite) {
            final KRewrite rew = (KRewrite) item;
            if (Stream.concat(
                    IncompleteCellUtils.flattenCells(rew.left()).stream(),
                    IncompleteCellUtils.flattenCells(rew.right()).stream())
                    .anyMatch(this::isCell)) {
                return term;
            }
        }
        KLabel computation = cfg.getCellLabel(cfg.getComputationCell());
        return IncompleteCellUtils.make(computation, false, item, true);
    }

    private boolean isCell(K k) {
        return k instanceof KApply
                && cfg.isCell(labelInfo.getCodomain(((KApply) k).klabel()));
    }
}
