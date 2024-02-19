// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import java.util.List;
import java.util.stream.Stream;
import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;

/**
 * If a SemanticSentence (Rule or Context) has a body that is not wrapped in any cell, wrap it in a
 * {@code <k>} cell
 */
public record AddImplicitComputationCell(ConfigurationInfo cfg, LabelInfo labelInfo) {

  public static Definition transformDefinition(Definition input) {
    ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
    LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
    return DefinitionTransformer.fromSentenceTransformer(
            new AddImplicitComputationCell(configInfo, labelInfo)::apply,
            "concretizing configuration")
        .apply(input);
  }

  public Sentence apply(Module m, Sentence s) {
    if (skipSentence(s)) {
      return s;
    }

    if (s instanceof RuleOrClaim rule) {
      return rule.newInstance(
          apply(rule.body(), m, rule instanceof Claim),
          rule.requires(),
          rule.ensures(),
          rule.att());
    } else if (s instanceof Context context) {
      return new Context(apply(context.body(), m, false), context.requires(), context.att());
    } else {
      return s;
    }
  }

  private boolean skipSentence(Sentence s) {
    return ExpandMacros.isMacro(s)
        || s.att().contains(Att.ANYWHERE())
        || s.att().contains(Att.SIMPLIFICATION());
  }

  // If there are multiple cells mentioned in the split configuration, we don't
  // apply the implicit <k> cell, unless the configuration is a claim and the second
  // cell mentioned is the automatically-added <generatedCounter> cell.
  private boolean shouldConsider(List<K> items, boolean isClaim) {
    if (items.size() == 1) {
      return !isClaim;
    } else if (items.size() == 2 && isClaim) {
      K second = items.get(1);
      if (second instanceof KApply app) {
        return app.klabel() == KLabels.GENERATED_COUNTER_CELL;
      }
    }

    return false;
  }

  private boolean canAddImplicitKCell(K item) {
    if (isCell(item)) {
      return false;
    }

    if (item instanceof final KRewrite rew) {
      return Stream.concat(
              IncompleteCellUtils.flattenCells(rew.left()).stream(),
              IncompleteCellUtils.flattenCells(rew.right()).stream())
          .noneMatch(this::isCell);
    }

    return true;
  }

  private K apply(K term, Module m, boolean isClaim) {
    if (m.isFunction(term)) return term;

    List<K> items = IncompleteCellUtils.flattenCells(term);
    if (!shouldConsider(items, isClaim)) {
      return term;
    }

    K item = items.get(0);
    if (!canAddImplicitKCell(item)) {
      return term;
    }

    KLabel computation = cfg.getCellLabel(cfg.getComputationCell());
    return IncompleteCellUtils.make(computation, false, item, true);
  }

  private boolean isCell(K k) {
    return k instanceof KApply && cfg.isCell(labelInfo.getCodomain(((KApply) k).klabel()));
  }
}
