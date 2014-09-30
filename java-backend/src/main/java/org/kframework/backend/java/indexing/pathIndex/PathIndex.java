// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex;

import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.indexing.pathIndex.trie.PathIndexTrie;
import org.kframework.backend.java.indexing.pathIndex.visitors.CoolingRuleVisitor;
import org.kframework.backend.java.indexing.pathIndex.visitors.HeatingRuleVisitor;
import org.kframework.backend.java.indexing.pathIndex.visitors.RuleVisitor;
import org.kframework.backend.java.indexing.pathIndex.visitors.TermVisitor;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.utils.general.IndexingStatistics;

import java.io.Serializable;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.ArrayList;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;

/**
 * This class implements some variant of the Path Indexing technique.
 *
 * Author: Owolabi Legunsen
 * 1/8/14: 10:08 AM
 *
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
public class PathIndex implements RuleIndex, Serializable{
    private final Map<Integer, Rule> indexedRules;
    private final Definition definition;
    private PathIndexTrie trie;
    private final Set<Integer> outputRuleIndices = new LinkedHashSet<>();
    private final Set<Integer> inputRuleIndices = new LinkedHashSet<>();
    private TermVisitor termVisitor;
    private boolean hasNOKCellRules;
    private final JavaExecutionOptions options;

    public enum RuleType {
        COOLING,
        HEATING,
        OUT,
        IN,
        OTHER
    }

    /**
     * Builds an index for a given definition using the path indexing algorithm
     * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
     *              the future
     *
     */
    @Deprecated @Inject
    public PathIndex(Definition definition, JavaExecutionOptions options) {
        this.definition = definition;
        this.options = options;
        this.indexedRules = new LinkedHashMap<>();
        termVisitor = new TermVisitor(definition.context(), options, false);
        buildIndex();
    }

    /**
     * Constructs the index (a trie) data structure from all the rules in the definition.
     */
    @Override
    public void buildIndex() {
        Multimap<Integer, String> pStringMap = ArrayListMultimap.create();
        int count = 1;

        //Step 1. Get all the pStrings from each of the rules
        for (Rule rule : definition.rules()) {
            if (rule.containsAttribute("heat") || rule.containsAttribute("print")) {
                pStringMap.putAll(createRulePString(rule, count, RuleType.HEATING));
            } else if (rule.containsAttribute("cool")) {
                pStringMap.putAll(createRulePString(rule, count, RuleType.COOLING));
            } else if (rule.containsAttribute("stdout") || rule.containsAttribute("stderr")) {
                pStringMap.putAll(createRulePString(rule, count, RuleType.OUT));
            } else if (rule.containsAttribute("stdin")) {
                pStringMap.putAll(createRulePString(rule, count, RuleType.IN));
            } else {
                pStringMap.putAll(createRulePString(rule, count, RuleType.OTHER));
            }
            indexedRules.put(count, rule);
            count++;
        }

        assert indexedRules.size() == definition.rules().size();
//        printIndices(indexedRules, pStringMap);

        //Step 2. initialise the trie
        trie = new PathIndexTrie();

        //Step 3. add all the pStrings to the trie
        ArrayList<String> strings;
        for (Integer key : pStringMap.keySet()) {
            strings = (ArrayList<String>) pStringMap.get(key);
            for (String string : strings) {
                //pass the substring starting at 2 to prevent clashes with "@.", which represents
                // the root node
                trie.addIndex(trie.getRoot(), string.substring(2), key);
            }
        }
    }

    /**
     * Utility method for printing the indexed rules. Useful only for debugging.
     *
     * @param indexedRules Mapping of Rules to the integers used to refer to them.
     * @param pString      Mapping of Rule number to the pStrings derived from a rule.
     */
    private void printIndices(Map<Integer, Rule> indexedRules, Multimap<Integer,
            String> pString) {
        for (Integer n : indexedRules.keySet()) {
            System.out.println("Rule " + n + ": ");
            System.out.println(indexedRules.get(n));
            System.out.println("Rule Attribute:");
            System.out.println(indexedRules.get(n).getAttributes());
            System.out.println("P-Strings: ");
            ArrayList<String> p_strings = (ArrayList<String>) pString.get(n);
            //There should be no null p-string!!
            if (p_strings != null) {
                for (int i = 0; i < p_strings.size(); i++) {
                    System.out.println((i + 1) + ": " + p_strings.get(i));
                }
            }
            System.out.println();
        }
    }

    /**
     * This method creates pStrings from an input rule.
     *
     * @param rule The rule from which pStrings are to be extracted
     * @param n    The integer to be assigned to this rule in the Index structure
     * @param type The type of the rule, i.e., cooling, heating, etc.
     * @return A mapping of the rule index to the PStrings created from the input rule
     */
    private Multimap<Integer, String> createRulePString(Rule rule, int n, RuleType type) {
        Multimap<Integer, String> pStrings = ArrayListMultimap.create();
        RuleVisitor ruleVisitor;
        //for rules with multiple K cells
        ArrayList<Cell> kCells = new ArrayList<>();
        switch (type) {
            case COOLING:
                ruleVisitor = new CoolingRuleVisitor(rule, definition.context());
                break;
            case HEATING:
                ruleVisitor = new HeatingRuleVisitor(definition.context());
                break;
            case OTHER:
                ruleVisitor = new RuleVisitor(definition.context());
                break;
            case OUT:
                pStrings.put(n, "@.out");
                outputRuleIndices.add(n);
                return pStrings;
            case IN:
                pStrings.put(n, "@.in");
                inputRuleIndices.add(n);
                return pStrings;
            default:
                throw new IllegalArgumentException("Cannot create P-String for unknown rule type:"
                        + type);
        }

        rule.accept(ruleVisitor);

        pStrings.putAll(n, ruleVisitor.getpStrings());
        hasNOKCellRules |= ruleVisitor.isHasNOKCellRule();
        return pStrings;
    }

    /**
     * This method is called at every rewriting step in order to find which of the indexed rules may
     * may be applicable to the term at that step.
     *
     * @param term the term to be rewritten
     * @return a list of rules that can possibly match
     */
    @Override
    @Deprecated
    public List<Rule> getRules(Term term) {
        Set<String> pStrings;
//        System.out.println("term: "+term);
        if (options.indexingStats) {
            IndexingStatistics.getPStringFromTermStopWatch.reset();
            IndexingStatistics.getPStringFromTermStopWatch.start();
            pStrings = getPStringsFromTerm(term);
            IndexingStatistics.getPStringFromTermStopWatch.stop();
            IndexingStatistics.timesForGettingPStringsFromTerm.add(
                    IndexingStatistics.getPStringFromTermStopWatch.elapsed(TimeUnit.MICROSECONDS));
        } else {
            pStrings = getPStringsFromTerm(term);
        }

//        System.out.println("PStrings: "+pStrings);

        Set<Rule> rules = new LinkedHashSet<>();

        Set<Integer> currentMatch;
        Set<Integer> matchingIndices = new LinkedHashSet<>();
        String subString;

        if (options.indexingStats) {
            IndexingStatistics.findMatchingIndicesStopWatch.reset();
            IndexingStatistics.findMatchingIndicesStopWatch.start();
        }
        for (String pString : pStrings) {
            String[] split = pString.split("\\.");
            int i = split.length;
            currentMatch = trie.retrieve(trie.getRoot(), pString);
            subString = pString;

            while (i > 0 && subString.lastIndexOf('.') > 1) {
                subString = pString.substring(0, subString.lastIndexOf('.') - 2);
                Set<Integer> retrievedIndices = trie.retrieve(trie.getRoot(), subString);
                if (retrievedIndices != null) {
                    currentMatch.addAll(retrievedIndices);
                }
            }

            if (currentMatch != null) {
                if (matchingIndices.isEmpty()) {
                    matchingIndices = currentMatch;
                } else {
                    //should it be an intersection?
                        matchingIndices.addAll(currentMatch);
                }
            }
        }

            if (matchingIndices != null && termVisitor.isAddOutputRules()) {
                matchingIndices.addAll(outputRuleIndices);
            }

            if (matchingIndices != null && termVisitor.isAddInputRules()) {
                matchingIndices.addAll(inputRuleIndices);
            }


        // this check is needed because of .K which now has  a pString of @.EMPTY_K, but may not
        // have any rules so indexed in some simpler languages like IMP
        if (matchingIndices != null) {
            for (Integer n : matchingIndices) {
                rules.add(indexedRules.get(n));
            }
        }

        if (options.indexingStats) {
            IndexingStatistics.findMatchingIndicesStopWatch.stop();
            IndexingStatistics.timesForFindingMatchingIndices.add(
                    IndexingStatistics.findMatchingIndicesStopWatch.elapsed(TimeUnit.MICROSECONDS));
        }

//        System.out.println("rules: "+rules +"\n");
        return new ArrayList<>(rules);
    }

    /**
     * Takes as input the term that is currently  being rewritten, traverses it and return a set
     * of strings that are used to query the index structure for finding possibly matching rules.
     *
     *
     * @param term  the term that is to be traversed
     * @return a set of positions that can be used to query the path index
     */
    private Set<String> getPStringsFromTerm(Term term) {
        termVisitor = new TermVisitor(definition.context(), options, hasNOKCellRules);
        term.accept(termVisitor);
        return termVisitor.getpStrings();
    }

    @Override
    public List<Rule> getRules(List<Cell<?>> indexingCells) {
        throw new UnsupportedOperationException();
    }
}