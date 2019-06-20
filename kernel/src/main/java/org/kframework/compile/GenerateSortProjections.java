// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.kframework.attributes.Att;
import org.kframework.Collections;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import scala.collection.Set;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class GenerateSortProjections {

    private Module mod;

    public Module gen(Module mod) {
        this.mod = mod;
        return Module(mod.name(), mod.imports(), (Set<Sentence>) mod.localSentences().$bar(stream(mod.definedSorts())
                .flatMap(this::gen).collect(Collections.toSet())), mod.att());
    }

    public static KLabel getProjectLbl(Sort sort, Module m) {
        KLabel lbl;
        lbl = KLabel("project:" + sort.toString());
        return lbl;
    }

    public Stream<? extends Sentence> gen(Sort sort) {
        if (RuleGrammarGenerator.isParserSort(sort) && !sort.equals(Sorts.KItem())) {
            return Stream.empty();
        }
        KLabel lbl = getProjectLbl(sort, mod);
        KVariable var = KVariable("K", Att.empty().add(Sort.class, sort));
        Rule r = Rule(KRewrite(KApply(lbl, var), var), BooleanUtils.TRUE, BooleanUtils.TRUE, Att().add("projection"));
        if (mod.definedKLabels().contains(lbl)) {
            return Stream.empty();
        }
        return stream(Set(Production(lbl, sort, Seq(Terminal(lbl.name()), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")), Att().add("function").add("projection")), r));
    }


}
