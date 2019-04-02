// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.FoldK;
import org.kframework.kore.TransformK;
import org.kframework.compile.checks.ComputeUnboundVariables;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import scala.collection.immutable.List;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveFunctionWithConfig {

    private Rule resolve(Rule rule, Module m) {
        return new Rule(
                transform(resolve(rule.body(), m), m),
                transform(rule.requires(), m),
                transform(rule.ensures(), m),
                rule.att());
    }

    private Context resolve(Context context, Module m) {
        return new Context(
                transform(context.body(), m),
                transform(context.requires(), m),
                context.att());
    }

    public static final KVariable CONFIG_VAR = KVariable("_Configuration", Att().add(Sort.class, Sorts.GeneratedTopCell()));

    private K transform(K term, Module module) {
      return new TransformK() {
        @Override
        public K apply(KApply kapp) {
          if (!kapp.items().isEmpty() && kapp.items().get(kapp.items().size() - 1).att().contains("withConfig")) {
            return super.apply(kapp);
          }
          if (module.attributesFor().get(kapp.klabel()).getOrElse(() -> Att()).contains("withConfig")) {
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
          if (!module.attributesFor().apply(funKApp.klabel()).contains(Attribute.FUNCTION_KEY)) {
            throw KEMException.compilerError("Found term that is not a cell or a function at the top of a rule.", fun);
          }
          if (!(cell instanceof KApply)) {
            throw KEMException.compilerError("Found term that is not a cell in the context of a function rule.", cell);
          }
          KApply cellKApp = (KApply)cell;
          K secondChild;
          if (cellKApp.klabel().equals(KLabels.GENERATED_TOP_CELL)) {
            secondChild = cell;
          } else {
            secondChild = IncompleteCellUtils.make(KLabels.GENERATED_TOP_CELL, true, cell, true);
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
        if (prod.att().contains("withConfig")) {
            List<ProductionItem> pis = Stream.concat(stream(prod.items()), Stream.of(NonTerminal(Sorts.GeneratedTopCell()))).collect(Collections.toList());
            return Production(prod.klabel(), prod.sort(), pis, prod.att());
        }
        return prod;
    }

    public K resolveConfigVar(K term) {
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
        }.apply(term) && new FoldK<Boolean>() {
            @Override
            public Boolean unit() {
                return false;
            }

            @Override
            public Boolean apply(KVariable k) {
                return k.name().equals("_Configuration");
            }

            @Override
            public Boolean merge(Boolean a, Boolean b) {
                return a || b;
            }
        }.apply(term)) {
            K left = RewriteToTop.toLeft(term);
            if (left instanceof KApply && ((KApply)left).klabel().equals(KLabels.GENERATED_TOP_CELL)) {
                term = KRewrite(KAs(RewriteToTop.toLeft(term), CONFIG_VAR), RewriteToTop.toRight(term));
            }
        }
        return term;
    }

    public Sentence resolveConfigVar(Sentence s) {
      if (s instanceof Rule) {
        Rule r = (Rule)s;
        return Rule(resolveConfigVar(r.body()), r.requires(), r.ensures(), r.att());
      }
      return s;
    }

    public Sentence resolve(Module m, Sentence s) {
        if (s instanceof Rule) {
            return resolve((Rule) s, m);
        } else if (s instanceof Context) {
            return resolve((Context) s, m);
        } else if (s instanceof Production) {
            return resolve((Production) s);
        } else {
            return s;
        }
    }
}
