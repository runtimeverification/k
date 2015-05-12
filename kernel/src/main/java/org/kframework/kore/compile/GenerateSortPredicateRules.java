package org.kframework.kore.compile;

import org.kframework.Collections;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.StringUtil;
import scala.collection.immutable.Set;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.Att;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Generates sort predicates from the subsort hierarchy of the module. This module assumes that the backend implements
 * the following rules:
 * isSort(#token(Sort, _)) => true
 * isK(K) => true
 * isKItem(K1(K2)) => true
 * isKItem(#token(_, _)) => true
 *
 * plus one sort membership function for each builtin-hooked sort.
 */
public class GenerateSortPredicateRules {

    private final Definition def;
    private Module mod;

    public GenerateSortPredicateRules(Definition def) {
        this.def = def;
    }

    public Module gen(Module mod) {
        this.mod = mod;
        return Module(mod.name(), mod.imports(), (Set<Sentence>) mod.localSentences().$bar(stream(mod.definedSorts())
                .flatMap(this::gen).collect(Collections.toSet())), mod.att());
    }

    private Stream<? extends Sentence> gen(Sort sort) {
        List<Sentence> res = new ArrayList<>();
        Production prod = Production("is" + sort.name(), Sorts.Bool(),
                Seq(Terminal("is" + sort.name()), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")),
                Att().add(Attribute.FUNCTION_KEY).add(Attribute.PREDICATE_KEY, sort.name()));
        res.add(prod);
        if (!RuleGrammarGenerator.isParserSort(sort)) {
            for (Sort bigSort : iterable(mod.subsorts().relations().apply(sort))) {
                if (!RuleGrammarGenerator.isParserSort(bigSort)) {
                    Rule subsort = Rule(KRewrite(KApply(KLabel("is" + bigSort.name()), KVariable("K", Att().add(Attribute.SORT_KEY, sort.name()))), BooleanUtils.TRUE), KApply(KLabel("is" + sort.name()), KVariable("K", Att().add(Attribute.SORT_KEY, sort.name()))), BooleanUtils.TRUE);
                    res.add(subsort);
                }
            }
        }
        for (Production p : stream(mod.productions()).filter(p -> p.sort().equals(sort)).collect(Collectors.toSet())) {
            if (p.klabel().isDefined() && !p.att().contains(Attribute.FUNCTION_KEY)) {
                if (!RuleGrammarGenerator.isParserSort(p.sort())) {
                    List<K> klist = new ArrayList<>();
                    List<K> side = new ArrayList<>();
                    int i = 0;
                    List<NonTerminal> nts = stream(p.items()).filter(pi -> pi instanceof NonTerminal).map(pi -> (NonTerminal) pi).collect(Collectors.toList());
                    for (NonTerminal nt : nts) {
                        KVariable v = KVariable("K" + i++);
                        klist.add(v);
                        side.add(KApply(KLabel("is" + nt.sort().name()), v));
                    }
                    ;
                    Optional<K> sideCondition = side.stream().reduce(BooleanUtils::and);
                    K requires;
                    if (!sideCondition.isPresent()) {
                        requires = BooleanUtils.TRUE;
                    } else {
                        requires = sideCondition.get();
                    }
                    Rule r = Rule(KRewrite(KApply(KLabel("is" + sort.name()), KApply(p.klabel().get(), KList(klist))), BooleanUtils.TRUE), requires, BooleanUtils.TRUE);
                    res.add(r);
                }
            }
        }
        res.add(Rule(KRewrite(KApply(KLabel("is" + sort.name()), KApply(KLabel("#KToken"), KToken(sort.name(), Sorts.KString()), KVariable("_"))), BooleanUtils.TRUE),
                BooleanUtils.TRUE,
                BooleanUtils.TRUE));
        res.add(Rule(KRewrite(KApply(KLabel("is" + sort.name()), KVariable("K")), BooleanUtils.FALSE), BooleanUtils.TRUE, BooleanUtils.TRUE, Att().add("owise")));
        return res.stream();
    }
}
