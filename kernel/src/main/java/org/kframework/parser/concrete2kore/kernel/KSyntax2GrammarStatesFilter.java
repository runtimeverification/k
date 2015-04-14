// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.kernel;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.BasicAutomata;
import dk.brics.automaton.RegExp;
import dk.brics.automaton.SpecialOperations;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.RegexTerminal;
import org.kframework.definition.Terminal;
import org.kframework.kil.loader.Constants;
import org.kframework.kore.Sort;
import org.kframework.parser.concrete2kore.kernel.Grammar.NextableState;
import org.kframework.parser.concrete2kore.kernel.Grammar.NonTerminal;
import org.kframework.parser.concrete2kore.kernel.Grammar.RuleState;
import org.kframework.parser.concrete2kore.kernel.Rule.WrapLabelRule;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.Collections.iterable;
import static org.kframework.Collections.stream;

/**
 * A simple visitor that goes through every accessible production and creates the NFA states for the
 * parser. First step is to create a NonTerminal object for every declared syntactic sort. These
 * will be referenced each time a NonTerminalState is created.
 */
public class KSyntax2GrammarStatesFilter {

    public static Grammar getGrammar(Module module) {
        Grammar grammar = new Grammar();
        Set<String> rejects = new HashSet<>();
        // create a NonTerminal for every declared sort
        for (Sort sort : iterable(module.definedSorts())) {
            grammar.add(new NonTerminal(sort.name()));
        }

        stream(module.productions()).forEach(p -> collectRejects(p, rejects));
        stream(module.productions()).collect(Collectors.groupingBy(p -> p.sort())).forEach((sort, prods) -> processProductions(sort, prods, grammar, rejects));

        grammar.addWhiteSpace();
        grammar.compile();
        return grammar;
    }

    static public <E> String mkString(Iterable<E> list, Function<E,String> stringify, String delimiter) {
        int i = 0;
        StringBuilder s = new StringBuilder();
        for (E e : list) {
            if (i != 0) { s.append(delimiter); }
            s.append(stringify.apply(e));
            i++;
        }
        return s.toString();
    }

    private static void collectRejects(Production prd, Set<String> rejects) {
        for (ProductionItem prdItem : iterable(prd.items())) {
            String pattern = "";
            if (prdItem instanceof Terminal) {
                if (!((Terminal) prdItem).value().equals("")) {
                    rejects.add(((Terminal) prdItem).value());
                }
            }
        }
    }

    public static void processProductions(Sort sort, List<Production> prods, Grammar grammar, Set<String> autoRejects) {
        NonTerminal nt = grammar.get(sort.name());
        assert nt != null : "Could not find in the grammar the required sort: " + sort;
        // all types of production follow pretty much the same pattern
        // previous = entryState
        // loop: add a new State to the 'previous' state; update 'previous' state

        // just a normal production with Terminals and Sort alternations
        // this will create a labeled KApp with the same arity as the
        // production

        Map<Production, NextableState> productionsRemaining = prods.stream().collect(Collectors.toMap(p -> p, p -> nt.entryState));
        class Holder {
            int i = 0;
        }
        final Holder h = new Holder();
        while (productionsRemaining.size() > 0) {
            Map<Pair<ProductionItem, NextableState>, List<Production>> productionsAtPosition = productionsRemaining.keySet().stream()
                    .collect(Collectors.groupingBy(p -> Pair.of(p.items().apply(h.i), productionsRemaining.get(p))));
            for (Pair<ProductionItem, NextableState> pair : productionsAtPosition.keySet()) {
                ProductionItem prdItem = pair.getKey();
                NextableState previous = pair.getValue();
                if (prdItem instanceof Terminal) {
                    Terminal terminal = (Terminal) prdItem;
                    Grammar.PrimitiveState pstate = new Grammar.RegExState(sort + ": " + terminal.value(), nt,
                            BasicAutomata.makeEmpty(), BasicAutomata.makeString(terminal.value()), getAutomaton(terminal.followPattern()));
                    previous.next.add(pstate);
                    RuleState del = new RuleState("DelTerminalRS", nt, new Rule.DeleteRule(1));
                    pstate.next.add(del);
                    previous = del;
                } else if (prdItem instanceof org.kframework.definition.NonTerminal) {
                    org.kframework.definition.NonTerminal srt = (org.kframework.definition.NonTerminal) prdItem;
                    Grammar.NonTerminalState nts = new Grammar.NonTerminalState(sort + " ::= " + srt.sort(), nt,
                            grammar.get(srt.sort().name()), false);
                    previous.next.add(nts);
                    previous = nts;
                } else if (prdItem instanceof RegexTerminal) {
                    RegexTerminal lx = (RegexTerminal) prdItem;
                    String pattern = null;
                    try {
                        pattern = lx.precedePattern();
                        Automaton precedeAuto = getAutomaton(lx.precedePattern());
                        SpecialOperations.reverse(precedeAuto);
                        pattern = lx.regex();
                        Automaton patternAuto = getAutomaton(lx.regex());
                        pattern = lx.followPattern();
                        Automaton followsAuto = getAutomaton(lx.followPattern());
                        Grammar.PrimitiveState pstate = new Grammar.RegExState(
                                sort.name() + ":" + lx.regex() + "(?!" + lx.followPattern() + ")",
                                nt,
                                precedeAuto,
                                patternAuto,
                                followsAuto);
                        RuleState del = new RuleState("DelRegexTerminalRS", nt, new Rule.DeleteRule(1));
                        previous.next.add(pstate);
                        pstate.next.add(del);
                        previous = del;
                    } catch (IllegalArgumentException e) {
                        throw KExceptionManager.criticalError("Could not compile regex: " + pattern + ", " + e.getMessage(), e);
                    }
                } else {
                    assert false : "Didn't expect this ProductionItem type: "
                            + prdItem.getClass().getName();
                }
                for (Production p : productionsAtPosition.get(pair)) {
                    productionsRemaining.put(p, previous);
                }
            }
            h.i++;
            Iterator<Production> iter = productionsRemaining.keySet().iterator();
            while(iter.hasNext()) {
                Production prd = iter.next();
                NextableState previous = productionsRemaining.get(prd);
                if (prd.items().size() == h.i) {
                    Automaton pattern = null;
                    Set<String> rejects = new HashSet<>();
                    if (prd.att().contains("token")) {
                        // TODO: calculate reject list
                        if (prd.att().contains(Constants.AUTOREJECT))
                            rejects = autoRejects;
                        if (prd.att().contains(Constants.REJECT2))
                            pattern = getAutomaton(prd.att().get(Constants.REJECT2).get().toString());
                    }
                    RuleState labelRule = new RuleState("AddLabelRS", nt, new WrapLabelRule(prd, pattern, rejects));
                    previous.next.add(labelRule);
                    previous = labelRule;

                    previous.next.add(nt.exitState);

                    iter.remove();
                }
            }
        }
    }

    public static void clearCache() {
        cache.clear();
    }

    private static Map<String, Automaton> cache = new HashMap<>();

    private static Automaton getAutomaton(String regex) {
        Automaton res = cache.get(regex);
        if (res == null) {
            res = new RegExp(regex).toAutomaton();
            cache.put(regex, res);
        }
        return res;
    }
}
