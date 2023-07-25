// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.backend.kore.ConstructorChecks;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Hooks;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.definition.Tag;
import org.kframework.definition.Terminal;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.unparser.Formatter;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Seq;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class AddKoreAttributes {

    private final Module module;
    private final KompileOptions options;

    public AddKoreAttributes(Module m, KompileOptions kompileOptions) {
        this.module = m;
        this.options = kompileOptions;
    }

    private boolean isFunction(Production prod) {
        return prod.att().contains(Att.FUNCTION());
    }

    private KList getAssoc(scala.collection.Set<Tuple2<Tag, Tag>> assoc, KLabel klabel) {
        return KList(stream(assoc).filter(t -> t._1().name().equals(klabel.name())).map(t -> KApply(KLabel(t._2().name()))).collect(Collectors.toList()));
    }

    private boolean isRealHook(Att att) {
        String hook = att.get(Att.HOOK());
        if (hook.startsWith("ARRAY.")) {
            return false;
        }
        if (options.hookNamespaces.stream().anyMatch(ns -> hook.startsWith(ns + "."))) {
            return true;
        }
        return Hooks.namespaces.stream().anyMatch(ns -> hook.startsWith(ns + "."));
    }

    public static final Production INJ_PROD = Production(KLabel(KLabels.INJ, Sort("S1"), Sort("S2")), Sort("S2"), Seq(NonTerminal(Sort("S1"))), Att());

    private Production production(KApply term) {
        return production(term, false);
    }
    private Production production(KApply term, boolean instantiatePolySorts) {
        KLabel klabel = term.klabel();
        if (klabel.name().equals(KLabels.INJ))
            return instantiatePolySorts ? INJ_PROD.substitute(term.klabel().params()) : INJ_PROD;
        Option<scala.collection.Set<Production>> prods = module.productionsFor().get(klabel.head());
        if (!(prods.nonEmpty() && prods.get().size() == 1))
            throw KEMException.compilerError("Expected to find exactly one production for KLabel: " + klabel + " found: " + prods.getOrElse(Collections::Set).size());
        return instantiatePolySorts ? prods.get().head().substitute(term.klabel().params()) : prods.get().head();
    }

    public synchronized Sentence add(Sentence s) {
        if (!(s instanceof Production))
            return s;

        Production prod = (Production) s;

        SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
        for (Rule rule : iterable(module.sortedRules())) {
            K left = RewriteToTop.toLeft(rule.body());

            if (left instanceof KApply) {
                KApply kapp = (KApply) left;
                    Production prod2 = production(kapp);
                    if (prod2.att().contains(Att.FUNCTION()) || rule.att().contains(Att.ANYWHERE())
                            || ExpandMacros.isMacro(rule)) {
                        functionRules.put(kapp.klabel(), rule);
                    }
            }
        }

        Set<Production> overloads = new HashSet<>();
        for (Production lesser : iterable(module.overloads().elements())) {
            for (Production greater : iterable(module.overloads().relations().get(lesser).getOrElse(Collections::<Production>Set))) {
                overloads.add(greater);
            }
        }

        boolean isFunctional = !isFunction(prod) || prod.att().contains(Att.TOTAL());
        boolean isConstructor = !isFunction(prod);
        isConstructor &= !prod.att().contains(Att.ASSOC());
        isConstructor &= !prod.att().contains(Att.COMM());
        isConstructor &= !prod.att().contains(Att.IDEM());
        isConstructor &= !(prod.att().contains(Att.FUNCTION()) && prod.att().contains(Att.UNIT()));

        // Later we might set !isConstructor because there are anywhere rules,
        // but if a symbol is a constructor at this point, then it is still
        // injective.
        boolean isInjective = isConstructor;

        boolean isMacro = false;
        boolean isAnywhere = overloads.contains(prod);
        if (prod.klabel().isDefined()) {
            for (Rule r : functionRules.get(prod.klabel().get())) {
                isMacro |= ExpandMacros.isMacro(r);
                isAnywhere |= r.att().contains(Att.ANYWHERE());
            }
        }
        isConstructor &= !isMacro;
        isConstructor &= !isAnywhere;

        Att att = prod.att().remove(Att.CONSTRUCTOR());
        if (att.contains(Att.HOOK()) && !isRealHook(att)) {
            att = att.remove(Att.HOOK());
        }
        if (isConstructor) {
            att = att.add(Att.CONSTRUCTOR());
        }
        if (isFunctional) {
            att = att.add(Att.FUNCTIONAL());
        }
        if (isAnywhere) {
            att = att.add(Att.ANYWHERE());
        }
        if (isInjective) {
            att = att.add(Att.INJECTIVE());
        }
        if (isMacro) {
            att = att.add(Att.MACRO());
        }
        // update format attribute with structure expected by backend
        String format = att.getOptional(Att.FORMAT()).orElse(Formatter.defaultFormat(prod.items().size()));
        int nt = 1;
        boolean hasFormat = true;
        boolean printName = stream(prod.items()).noneMatch(pi -> pi instanceof NonTerminal && ((NonTerminal) pi).name().isEmpty());
        boolean printEllipses = false;

        for (int i = 0; i < prod.items().size(); i++) {
            if (prod.items().apply(i) instanceof NonTerminal) {
                String replacement;
                if (printName && prod.isPrefixProduction()) {
                    replacement = ((NonTerminal) prod.items().apply(i)).name().get() + ": %" + (nt++);
                    printEllipses = true;
                } else {
                    replacement = "%" + (nt++);
                }
                format = format.replaceAll("%" + (i+1) + "(?![0-9])", replacement);
            } else if (prod.items().apply(i) instanceof Terminal) {
                format = format.replaceAll("%" + (i+1) + "(?![0-9])", "%c" + ((Terminal)prod.items().apply(i)).value().replace("\\", "\\\\").replace("$", "\\$").replace("%", "%%") + "%r");
            } else {
                hasFormat = false;
            }
        }
        if (printEllipses && format.contains("(")) {
            int idxLParam = format.indexOf("(") + 1;
            format = format.substring(0, idxLParam) + "... " + format.substring(idxLParam);
        }
        if (hasFormat) {
            att = att.add(Att.FORMAT(), format);
            if (att.contains(Att.COLOR())) {
                boolean escape = false;
                StringBuilder colors = new StringBuilder();
                String conn = "";
                for (int i = 0; i < format.length(); i++) {
                    if (escape && format.charAt(i) == 'c') {
                        colors.append(conn).append(att.get(Att.COLOR()));
                        conn = ",";
                    }
                    if (format.charAt(i) == '%') {
                        escape = true;
                    } else {
                        escape = false;
                    }
                }
                att = att.add(Att.COLORS(), colors.toString());
            }
            StringBuilder sb = new StringBuilder();
            for (ProductionItem pi : iterable(prod.items())) {
                if (pi instanceof NonTerminal) {
                    sb.append('0');
                } else {
                    sb.append('1');
                }
            }
            att = att.add(Att.TERMINALS(), sb.toString());
            if (prod.klabel().isDefined()) {
                List<K> lessThanK = new ArrayList<>();
                Option<scala.collection.Set<Tag>> lessThan = module.priorities().relations().get(Tag(prod.klabel().get().name()));
                if (lessThan.isDefined()) {
                    for (Tag t : iterable(lessThan.get())) {
                        if (ConstructorChecks.isBuiltinLabel(KLabel(t.name()))) {
                            continue;
                        }
                        lessThanK.add(KApply(KLabel(t.name())));
                    }
                }
                att = att.add(Att.PRIORITIES(), KList.class, KORE.KList(lessThanK));
                att = att.remove(Att.LEFT());
                att = att.remove(Att.RIGHT());
                att = att.add(Att.LEFT(), KList.class, getAssoc(module.leftAssoc(), prod.klabel().get()));
                att = att.add(Att.RIGHT(), KList.class, getAssoc(module.rightAssoc(), prod.klabel().get()));
            }
        } else {
            att = att.remove(Att.FORMAT());
        }

        // This attribute is a frontend attribute only and is removed from the kore
        // Since it has no meaning outside the frontend
        att.remove(Att.ORIGINAL_PRD(), Production.class);
        return prod.withAtt(att);
    }
}
