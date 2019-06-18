// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.Collections;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import scala.Option;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveStrict {

    private final KompileOptions kompileOptions;
    private final Definition d;

    public ResolveStrict(KompileOptions kompileOptions, Definition d) {
        this.kompileOptions = kompileOptions;
        this.d = d;
    }

    public Set<Sentence> resolve(Set<Production> strictProductions) {
        Set<Sentence> sentences = new HashSet<>();
        for (Production prod : strictProductions) {
            if (!prod.klabel().isDefined()) {
                throw KEMException.compilerError("Only productions with a KLabel can be strict.", prod);
            }
            if (prod.att().contains(Attribute.STRICT_KEY)) {
                sentences.addAll(resolve(prod, false));
            }
            if (prod.att().contains(Attribute.SEQSTRICT_KEY)) {
                sentences.addAll(resolve(prod, true));
            }
        }
        return sentences;
    }

    private static KApply cast(Sort sort, K k) {
        return KApply(KLabel("#SemanticCastTo" + sort.toString()), k);
    }

    public static void setPositions(String attribute, List<Integer> strictnessPositions, long arity, Production loc) {
        String[] strictAttrs = attribute.split(",");
        for (String strictAttr : strictAttrs) {
            try {
                int pos = Integer.parseInt(strictAttr.trim());
                if (pos < 1 || pos > arity)
                    throw new IndexOutOfBoundsException();
                strictnessPositions.add(pos);
            } catch (NumberFormatException | IndexOutOfBoundsException e) {
                if (arity == 0) {
                    throw KEMException.compilerError("Cannot put a strict attribute on a production with no nonterminals", loc);
                } else {
                    throw KEMException.compilerError(
                        "Expecting a number between 1 and " + arity + ", but found " + strictAttr + " as a" +
                                " strict position in " + Arrays.toString(strictAttrs),
                        loc);
                }
            }
        }
    }

    private void setAliases(String attribute, Set<ContextAlias> aliases, Production prod) {
        String[] strictAttrs = attribute.split(",");
        for (String strictAttr : strictAttrs) {
            String label = strictAttr.trim();
            Option<scala.collection.Set<Sentence>> ss = d.mainModule().labeled().get(label);
            if (ss.isDefined()) {
                for (Sentence s : iterable(ss.get())) {
                    if (s instanceof ContextAlias) {
                        aliases.add((ContextAlias)s);
                    } else {
                        throw KEMException.compilerError("Found rule label \"" + label + "\" in strictness attribute of production " + prod + " which does not refer to a context alias.", s);
                    }
                }
            } else {
                throw KEMException.compilerError("Found rule label \"" + label + "\" in strictness attribute which did not refer to any sentence.", prod);
            }
        }

    }

    private static final ContextAlias DEFAULT_ALIAS = ContextAlias(KVariable("HERE"), BooleanUtils.TRUE, Att.empty());

    public Set<Sentence> resolve(Production production, boolean sequential) {
        long arity = production.nonterminals().size();
        List<Integer> strictnessPositions = new ArrayList<>();
        Set<ContextAlias> aliases = new HashSet<>();
        String attribute;
        if (sequential) {
            attribute = production.att().get(Attribute.SEQSTRICT_KEY);
        } else {
            attribute = production.att().get(Attribute.STRICT_KEY);
        }
        if (attribute.isEmpty()) {
            for (int i = 1; i <= arity; i++) {
                strictnessPositions.add(i);
            }
            aliases.add(DEFAULT_ALIAS);
        } else {
            String[] components = attribute.split(";");
            if (components.length == 1) {
                if (Character.isDigit(components[0].trim().charAt(0))) {
                    aliases.add(DEFAULT_ALIAS);
                    setPositions(components[0].trim(), strictnessPositions, arity, production);
                } else {
                    for (int i = 1; i <= arity; i++) {
                        strictnessPositions.add(i);
                    }
                    setAliases(components[0].trim(), aliases, production);
                }
            } else if (components.length == 2) {
                setAliases(components[0].trim(), aliases, production);
                setPositions(components[1].trim(), strictnessPositions, arity, production);
            } else {
                throw KEMException.compilerError("Invalid strict attribute containing multiple semicolons.", production);
            }
        }

        Set<Sentence> sentences = new HashSet<>();
        for (int i = 0; i < strictnessPositions.size(); i++) {
            List<K> items = new ArrayList<>();
            for (int j = 0; j < arity; j++) {
                if (kompileOptions.strict()) {
                    // Preserve sort information of the production
                    items.add(cast(production.nonterminal(j).sort(), KVariable("K" + j)));
                } else {
                    items.add(KVariable("K" + j));
                }
            }
            int strictnessPosition = strictnessPositions.get(i) - 1;
            if (kompileOptions.strict()) {
                // Preserve sort information of the production
                items.set(strictnessPosition, cast(production.nonterminal(strictnessPosition).sort(), KVariable("HOLE")));
            } else {
                items.set(strictnessPosition, cast(Sorts.KItem(), KVariable("HOLE")));
            }

            // is seqstrict the elements before the argument should be KResult
            Optional<KApply> sideCondition = strictnessPositions.subList(0, i).stream().map(j -> KApply(KLabel("isKResult"), KVariable("K" + (j - 1)))).reduce(BooleanUtils::and);
            K requires;
            if (!sideCondition.isPresent() || !sequential) {
                requires = BooleanUtils.TRUE;
            } else {
                requires = sideCondition.get();
            }
            K here = KApply(production.klabel().get(), KList(items));
            for (ContextAlias alias : aliases) {
                K body = new TransformK() {
                    @Override
                    public K apply(KVariable var) {
                      if (var.name().equals("HERE")) {
                        return here;
                      }
                      return var;
                    }
                }.apply(alias.body());
                Context ctx = Context(body, BooleanUtils.and(requires, alias.requires()), production.att().addAll(alias.att()).remove("label"));
                sentences.add(ctx);
            }
        }
        if (production.att().contains("hybrid")) {
            List<K> items = new ArrayList<>();
            for (int j = 0; j < arity; j++) {
                if (kompileOptions.strict()) {
                    // Preserve sort information of the production
                    items.add(cast(production.nonterminal(j).sort(), KVariable("K" + j)));
                } else {
                    items.add(KVariable("K" + j));
                }
            }
            K term = KApply(production.klabel().get(), KList(items));
            Optional<KApply> sideCondition = strictnessPositions.stream().map(j -> KApply(KLabel("isKResult"), KVariable("K" + (j - 1)))).reduce(BooleanUtils::and);
            K requires;
            if (!sideCondition.isPresent()) {
                requires = BooleanUtils.TRUE;
            } else {
                requires = sideCondition.get();
            }
            Rule hybrid = Rule(KRewrite(KApply(KLabel("isKResult"), term), BooleanUtils.TRUE), requires, BooleanUtils.TRUE);
            sentences.add(hybrid);
        }
        return sentences;
    }

    public Module resolve(Module input) {
        Set<Sentence> contextsToAdd = resolve(stream(input.localSentences())
                .filter(s -> s instanceof Production)
                .map(s -> (Production) s)
                .filter(p -> p.att().contains("strict") || p.att().contains("seqstrict")).collect(Collectors.toSet()));
        return Module(input.name(), input.imports(), (scala.collection.Set<Sentence>) stream(input.localSentences()).filter(s -> !(s instanceof ContextAlias)).collect(Collections.toSet()).$bar(immutable(contextsToAdd)), input.att());
    }
}
