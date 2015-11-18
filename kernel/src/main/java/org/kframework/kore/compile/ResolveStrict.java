// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.Att;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveStrict {

    private final KompileOptions kompileOptions;

    public ResolveStrict(KompileOptions kompileOptions) {
        this.kompileOptions = kompileOptions;
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
        return KApply(KLabel("#SemanticCastTo" + sort.name()), k);
    }

    public Set<Sentence> resolve(Production production, boolean sequential) {
        long arity = stream(production.items()).filter(i -> i instanceof NonTerminal).count();
        List<Integer> strictnessPositions = new ArrayList<>();
        String attribute;
        if (sequential) {
            attribute = production.att().<String>get(Attribute.SEQSTRICT_KEY).get();
        } else {
            attribute = production.att().<String>get(Attribute.STRICT_KEY).get();
        }
        if (attribute.isEmpty()) {
            for (int i = 1; i <= arity; i++) {
                strictnessPositions.add(i);
            }
        } else {
            String[] strictAttrs = attribute.split(",");
            for (String strictAttr : strictAttrs) {
                try {
                    int pos = Integer.parseInt(strictAttr.trim());
                    if (pos < 1 || pos > arity)
                        throw new IndexOutOfBoundsException();
                    strictnessPositions.add(pos);
                } catch (NumberFormatException | IndexOutOfBoundsException e) {
                    throw KEMException.compilerError(
                            "Expecting a number between 1 and " + arity + ", but found " + strictAttr + " as a" +
                                    " strict position in " + Arrays.toString(strictAttrs),
                            production);
                }
            }
        }

        Set<Sentence> contexts = new HashSet<>();
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
                items.set(strictnessPosition, cast(Sort("KItem"), KVariable("HOLE")));
            }

            // is seqstrict the elements before the argument should be KResult
            Optional<KApply> sideCondition = strictnessPositions.subList(0, i).stream().map(j -> KApply(KLabel("isKResult"), KVariable("K" + (j - 1)))).reduce(BooleanUtils::and);
            K requires;
            if (!sideCondition.isPresent() || !sequential) {
                requires = BooleanUtils.TRUE;
            } else {
                requires = sideCondition.get();
            }
            Context ctx = Context(KApply(production.klabel().get(), KList(items)), requires, Att());
            contexts.add(ctx);
        }
        return contexts;
    }

    public Module resolve(Module input) {
        Set<Sentence> contextsToAdd = resolve(stream(input.localSentences())
                .filter(s -> s instanceof Production)
                .map(s -> (Production) s)
                .filter(p -> p.att().contains("strict") || p.att().contains("seqstrict")).collect(Collectors.toSet()));
        return Module(input.name(), input.imports(), (scala.collection.Set<Sentence>) input.localSentences().$bar(immutable(contextsToAdd)), input.att());
    }
}
