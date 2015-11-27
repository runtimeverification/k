// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.LabelInfo;
import org.kframework.compile.LabelInfoFromModule;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;

import java.util.List;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 *  If a SemanticSentence (Rule or Context) has a body that is not wrapped in any cell,
 *  wrap it in a {@code <k>} cell
 */
public class AddImplicitComputationCell implements UnaryOperator<Sentence> {

    public static Definition transformDefinition(Definition input) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
        LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
        return DefinitionTransformer.fromSentenceTransformer(
                new AddImplicitComputationCell(configInfo, labelInfo),
                "concretizing configuration").apply(input);
    }

    private final ConfigurationInfo cfg;
    private final LabelInfo labelInfo;

    public AddImplicitComputationCell(ConfigurationInfo cfg, LabelInfo labelInfo) {
        this.cfg = cfg;
        this.labelInfo = labelInfo;
    }

    public Sentence apply(Sentence s) {
        if (s.att().contains(Attribute.MACRO_KEY) || s.att().contains(Attribute.ANYWHERE_KEY)) {
            return s;
        }

        if (s instanceof Rule) {
            Rule rule = (Rule) s;
            return new Rule(apply(rule.body()), rule.requires(), rule.ensures(), rule.att());
        } else if (s instanceof Context) {
            Context context = (Context) s;
            return new Context(apply(context.body()), context.requires(), context.att());
        } else {
            return s;
        }
    }

    private K apply(K term) {
        if (labelInfo.isFunction(term)) return term;

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
