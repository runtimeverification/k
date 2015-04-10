// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.Collections;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;

import java.util.ArrayList;
import java.util.List;

import static org.kframework.kore.KORE.*;

/**
 * Wrap a top cell around rules without an explicit top cell,
 * and wrap a k cell around a top-level rewrite
 */
// TODO anywhere rules and rules defining functions shouldn't be wrapped
public class AddImplicitCells {

    private final ConfigurationInfo cfg;
    private final LabelInfo labelInfo;

    public AddImplicitCells(ConfigurationInfo cfg, LabelInfo labelInfo) {
        this.cfg = cfg;
        this.labelInfo = labelInfo;
    }

    public K addImplicitCells(K term) {
        return addRootCell(addComputationCells(term));
    }

    protected K addComputationCells(K term) {
        KLabel computation = cfg.getCellLabel(cfg.getComputationCell());

        List<K> items = IncompleteCellUtils.flattenCells(term);
        if (items.size() != 1) {
            return term;
        }
        K item = items.get(0);
        if (item instanceof KApply && cfg.isCell(labelInfo.getCodomain(((KApply) item).klabel()))) {
            return term;
        } else {
            return IncompleteCellUtils.make(computation, false, item, true);
        }
    }

    protected K addRootCell(K term) {
        KLabel root = cfg.getCellLabel(cfg.getRootCell());

        if (term instanceof KApply && ((KApply) term).klabel().equals(root)) {
            return term;
        } else {
            return IncompleteCellUtils.make(root, true, term, true);
        }
    }

    public Rule addImplicitCells(Rule rule) {
        return new Rule(
                addImplicitCells(rule.body()),
                rule.requires(),
                rule.ensures(),
                rule.att());
    }

    public Context addImplicitCells(Context context) {
        return new Context(
                addImplicitCells(context.body()),
                context.requires(),
                context.att());
    }

    public Sentence addImplicitCells(Sentence s) {
        if (s instanceof Rule) {
            return addImplicitCells((Rule) s);
        } else if (s instanceof Context) {
            return addImplicitCells((Context) s);
        } else {
            return s;
        }
    }

    ModuleTransformer moduleTransormer = ModuleTransformer.from(this::addImplicitCells);

    public Module addImplicitCells(Module m) {
        return moduleTransormer.apply(m);
    }
}
