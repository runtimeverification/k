// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.FoldK;
import org.kframework.kore.TransformK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import scala.collection.immutable.List;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveFunctionWithConfig {

    private final Set<KLabel> withConfigFunctions = new HashSet<>();
    private final Sort topCell;
    private final KLabel topCellLabel;

    public ResolveFunctionWithConfig(Definition d, boolean kore) {
      this(d.mainModule(), kore);
    }

    public ResolveFunctionWithConfig(Module mod, boolean kore) {
      ComputeTransitiveFunctionDependencies deps = new ComputeTransitiveFunctionDependencies(mod);
      Set<KLabel> functions = stream(mod.productions()).filter(p -> p.att().contains(Att.FUNCTION())).map(p -> p.klabel().get()).collect(Collectors.toSet());
      withConfigFunctions.addAll(functions.stream().filter(f -> stream(mod.rulesFor().getOrElse(f, () -> Collections.<Rule>Set())).anyMatch(r -> ruleNeedsConfig(r))).collect(Collectors.toSet()));
      withConfigFunctions.addAll(deps.ancestors(withConfigFunctions));
      ConfigurationInfoFromModule info = new ConfigurationInfoFromModule(mod);
      if (kore) {
        topCell = Sorts.GeneratedTopCell();
        topCellLabel = KLabels.GENERATED_TOP_CELL;
      } else {
        topCell = info.getRootCell();
        topCellLabel = info.getCellLabel(topCell);
      }
      CONFIG_VAR = KVariable("#Configuration", Att().add(Sort.class, topCell).add("withConfig"));
    }

    private boolean ruleNeedsConfig(RuleOrClaim r) {
        if (r.body() instanceof KApply && ((KApply)r.body()).klabel().name().equals("#withConfig")) {
            return true;
        }
        FoldK<Boolean> hasVarNeedsConfig = new FoldK<Boolean>() {
            @Override
            public Boolean unit() {
                return false;
            }

            @Override
            public Boolean merge(Boolean a, Boolean b) {
                return a || b;
            }

            @Override
            public Boolean apply(KVariable k) {
                return k.name().startsWith("!") || k.name().equals("#Configuration");
            }
        };
        if (hasVarNeedsConfig.apply(RewriteToTop.toRight(r.body())) || hasVarNeedsConfig.apply(r.requires()) || hasVarNeedsConfig.apply(r.ensures())) {
            return true;
        }
        return false;
    }

    public RuleOrClaim resolve(RuleOrClaim rule, Module m) {
        return rule.newInstance(
                transform(resolve(rule.body(), m), m),
                transform(rule.requires(), m),
                transform(rule.ensures(), m),
                rule.att());
    }

    public Context resolve(Context context, Module m) {
        return new Context(
                transform(context.body(), m),
                transform(context.requires(), m),
                context.att());
    }

    public ContextAlias resolve(ContextAlias context, Module m) {
        return new ContextAlias(
                transform(context.body(), m),
                transform(context.requires(), m),
                context.att());
    }

    public final KVariable CONFIG_VAR;

    private K transform(K term, Module module) {
      return new TransformK() {
        @Override
        public K apply(KApply kapp) {
          if (!kapp.items().isEmpty() && kapp.items().get(kapp.items().size() - 1).att().contains("withConfig")) {
            return super.apply(kapp);
          }
          if (withConfigFunctions.contains(kapp.klabel())) {
            return KApply(kapp.klabel(), KList(Stream.concat(kapp.items().stream().map(this::apply), Stream.of(CONFIG_VAR)).collect(Collections.toList())), kapp.att());
          }
          return super.apply(kapp);
        }
      }.apply(term);
    }

    private K resolve(K body, Module module) {
      if (body instanceof KApply) {
        KApply kapp = (KApply) body;
        if (kapp.klabel().name().equals("#withConfig")) {
          K fun = kapp.items().get(0);
          K cell = kapp.items().get(1);
          K rhs = null;
         KRewrite rew = null;
          if (fun instanceof KRewrite) {
            rew = (KRewrite)fun;
            fun = rew.left();
            rhs = rew.right();
          }
          if (!(fun instanceof KApply)) {
            throw KEMException.compilerError("Found term that is not a cell or a function at the top of a rule.", fun);
          }
          KApply funKApp = (KApply)fun;
          if (!module.attributesFor().apply(funKApp.klabel()).contains(Att.FUNCTION())) {
            throw KEMException.compilerError("Found term that is not a cell or a function at the top of a rule.", fun);
          }
          if (!(cell instanceof KApply)) {
            throw KEMException.compilerError("Found term that is not a cell in the context of a function rule.", cell);
          }
          KApply cellKApp = (KApply)cell;
          K secondChild;
          if (cellKApp.klabel().equals(topCellLabel)) {
            secondChild = cell;
          } else {
            secondChild = IncompleteCellUtils.make(topCellLabel, true, cell, true);
          }
          List<K> items = Stream.concat(funKApp.items().stream(), Stream.of(KAs(secondChild, CONFIG_VAR, Att().add("withConfig")))).collect(Collections.toList());
          K result = KApply(funKApp.klabel(), KList(items), funKApp.att());
          if (rhs == null) {
            return result;
          } else {
            return KRewrite(result, rhs, rew.att());
          }
        }
      }
      return body;
    }

    private Production resolve(Production prod) {
        if (prod.klabel().isDefined() && withConfigFunctions.contains(prod.klabel().get())) {
            List<ProductionItem> pis = Stream.concat(stream(prod.items()), Stream.of(NonTerminal(topCell))).collect(Collections.toList());
            return Production(prod.klabel(), prod.params(), prod.sort(), pis, prod.att());
        }
        return prod;
    }

    public K resolveConfigVar(K body, K requires, K ensures) {
      FoldK<Boolean> hasConfig = new FoldK<Boolean>() {
          @Override
          public Boolean unit() {
              return false;
          }

          @Override
          public Boolean apply(KVariable k) {
              return k.name().equals("#Configuration");
          }

          @Override
          public Boolean merge(Boolean a, Boolean b) {
              return a || b;
          }
      };
      if (new FoldK<Boolean>() {
            @Override
            public Boolean unit() {
                return false;
            }

            @Override
            public Boolean apply(KRewrite k) {
                return true;
            }

            @Override
            public Boolean merge(Boolean a, Boolean b) {
                return a || b;
            }
        }.apply(body) && (hasConfig.apply(body) || hasConfig.apply(requires) || hasConfig.apply(ensures))) {
            K left = RewriteToTop.toLeft(body);
            if (left instanceof KApply && ((KApply)left).klabel().equals(topCellLabel)) {
                body = KRewrite(KAs(RewriteToTop.toLeft(body), CONFIG_VAR), RewriteToTop.toRight(body));
            }
        }
        return body;
    }

    public Sentence resolveConfigVar(Sentence s) {
      if (s instanceof RuleOrClaim) {
        RuleOrClaim r = (RuleOrClaim)s;
        return r.newInstance(resolveConfigVar(r.body(), r.requires(), r.ensures()), r.requires(), r.ensures(), r.att());
      }
      return s;
    }

    public Module moduleResolve(Module m) {
        Set<Sentence> newSentences = new HashSet<>();
        for (Sentence s : mutable(m.localSentences())) {
            if (s instanceof RuleOrClaim) {
                newSentences.add(resolve((RuleOrClaim) s, m));
            } else if (s instanceof Context) {
                newSentences.add(resolve((Context) s, m));
            } else if (s instanceof ContextAlias) {
                newSentences.add(resolve((ContextAlias) s, m));
            } else if (s instanceof Production) {
                Production prd = resolve((Production) s);
                newSentences.add(prd);
                // topCell introduces a new sort. Make sure it's declared
                if (!prd.equals(s) && !m.definedSorts().contains(topCell.head()))
                    newSentences.add(SyntaxSort(Seq(), topCell));
            } else {
                newSentences.add(s);
            }
        }
        if (newSentences.equals(mutable(m.localSentences())))
            return m;
        return Module.apply(m.name(), m.imports(), immutable(newSentences), m.att());
    }
}
