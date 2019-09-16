// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.Sort;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * Created by dwightguth on 5/28/15.
 */
public class GenerateSortPredicateSyntax {

    public Module gen(Module mod) {
        Set<Sentence> res = new HashSet<>();
        for (Sort sort : iterable(mod.definedSorts())) {
            res.addAll(gen(mod, sort));
        }
        if (!res.isEmpty()) {
            res.add(SyntaxSort(Sorts.K()));
        }
        return Module(mod.name(), mod.imports(), (scala.collection.Set<Sentence>) mod.localSentences().$bar(immutable(res)), mod.att());
    }

    public Set<Sentence> gen(Module mod, Sort sort) {
        Production prod = Production(KLabel("is" + sort.toString()), Sorts.Bool(),
                Seq(Terminal("is" + sort.toString()), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")),
                Att().add(Attribute.FUNCTION_KEY).add(Attribute.PREDICATE_KEY, Sort.class, sort));
        if (!mod.productions().contains(prod))
            return Collections.singleton(prod);
        return Collections.emptySet();
    }
}
