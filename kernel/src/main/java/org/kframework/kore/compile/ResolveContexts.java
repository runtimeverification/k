// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.Collections;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.Att;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveContexts {



    public Module resolve(Module input) {
        Set<Sentence> rulesToAdd = stream(input.localSentences())
                .filter(s -> s instanceof Context)
                .map(s -> (Context) s)
                .flatMap(c -> this.resolve(c, input)).collect(Collectors.toCollection(HashSet::new));
        if (!rulesToAdd.isEmpty()) {
            rulesToAdd.add(SyntaxSort(Sort("K")));
        }
        return Module(input.name(), input.imports(), (scala.collection.immutable.Set<Sentence>) stream(input.localSentences()).filter(s -> !(s instanceof Context)).collect(Collections.toSet()).$bar(immutable(rulesToAdd)), input.att());
    }

    private Set<KLabel> klabels = new HashSet<>();
    private int counter = 0;

    private KLabel getUniqueFreezerLabel(Module input) {
        if (klabels.isEmpty()) {
            klabels.addAll(mutable(input.definedKLabels()));
        }
        KLabel freezer;
        do {
            freezer = KLabel("#freezer" + counter++);
        } while (klabels.contains(freezer));
        klabels.add(freezer);
        return freezer;
    }

    private Stream<? extends Sentence> resolve(Context context, Module input) {
        class Holder {
            K heated;
            SortedSet<KVariable> vars = new TreeSet<>((v1, v2) -> v1.name().compareTo(v2.name()));
        }
        if (!(context.body() instanceof KApply)) {
            throw KEMException.criticalError("Cannot compile a context which is not a KApply.", context);
        }
        Holder h = new Holder();
        K body = context.body();
        K requires = context.requires();
        new VisitKORE() {
            @Override
            public Void apply(KRewrite k) {
                if (h.heated != null) {
                    throw KEMException.compilerError("Cannot compile a context with multiple rewrites.", context);
                }
                h.heated = k.right();
                return super.apply(k);
            }

            @Override
            public Void apply(KVariable k) {
                if (!k.name().equals("HOLE")) {
                    h.vars.add(k);
                }
                return super.apply(k);
            }
        }.apply(body);
        if (h.heated == null) {
            h.heated = ResolveStrict.HOLE;
        }
        K cooled = RewriteToTop.toLeft(body);
        // TODO(dwightguth): generate freezers better for pretty-printing purposes
        List<ProductionItem> items = new ArrayList<>();
        KLabel freezerLabel = getUniqueFreezerLabel(input);
        items.add(Terminal(freezerLabel.name()));
        items.add(Terminal("("));
        for (int i = 0; i < h.vars.size(); i++) {
            items.add(NonTerminal(Sort("K")));
            items.add(Terminal(","));
        }
        items.remove(items.size() - 1);
        items.add(Terminal(")"));
        Production freezer = Production(freezerLabel.name(), input.sortFor().apply(((KApply) context.body()).klabel()), immutable(items), Att());
        K frozen = KApply(freezerLabel, h.vars.stream().map(v -> (K) v).collect(Collections.toList()));
        return Stream.of(freezer,
                Rule(KRewrite(cooled, KSequence(h.heated, frozen)), requires, BooleanUtils.TRUE, context.att().add("heat")),
                Rule(KRewrite(KSequence(h.heated, frozen), cooled), requires, BooleanUtils.TRUE, context.att().add("cool")));
    }
}
