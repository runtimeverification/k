// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;

import java.util.List;
import java.util.stream.Stream;

/**
 * This pass adds the implicit top and k cells to
 * the bodies of rules and contexts.
 * A K cell is added only if the body is a single item,
 * which is not already a cell or a rewrite on cells.
 * The top cell is added unless the body is already an
 * instance of the top cell.
 * Rules with the anywhere attribute are not modified.
 */
// TODO: rules defining functions shouldn't be wrapped
public class AddTopCellToRules {

    private final ConfigurationInfo cfg;
    private final LabelInfo labelInfo;

    public AddTopCellToRules(ConfigurationInfo cfg, LabelInfo labelInfo) {
        this.cfg = cfg;
        this.labelInfo = labelInfo;
    }

    public K addImplicitCells(K term) {
        if (labelInfo.isFunction(term)) return term;
        return addRootCell(term);
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
        if (s.att().contains(Attribute.MACRO_KEY) || s.att().contains(Attribute.ANYWHERE_KEY)) {
            return s;
        }
        if (s instanceof Rule) {
            return addImplicitCells((Rule) s);
        } else if (s instanceof Context) {
            return addImplicitCells((Context) s);
        } else {
            return s;
        }
    }
}
