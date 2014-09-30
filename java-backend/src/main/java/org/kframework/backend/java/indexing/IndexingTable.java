// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.Singleton;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Constants;

import java.io.Serializable;
import java.util.Set;
import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.LinkedHashSet;

/**
 * The indexing scheme currently used in the Java Backend
 */
public class IndexingTable implements Serializable, RuleIndex{

    private Map<Index, List<Rule>> ruleTable;
    private Map<Index, List<Rule>> heatingRuleTable;
    private Map<Index, List<Rule>> coolingRuleTable;
    private Map<Index, List<Rule>> instreamRuleTable;
    private Map<Index, List<Rule>> outstreamRuleTable;
    private Map<Index, List<Rule>> simulationRuleTable;
    private List<Rule> unindexedRules;
    private final Definition definition;

    private final Data data;

    @Singleton
    public static class Data implements Serializable {
        public final TopIndex TOP_INDEX = new TopIndex();
        public final IndexingPair TOP_INDEXING_PAIR = new IndexingPair(TOP_INDEX, TOP_INDEX);
        public final BottomIndex BOTTOM_INDEX = new BottomIndex();
        public final IndexingPair BOTTOM_INDEXING_PAIR = new IndexingPair(BOTTOM_INDEX, BOTTOM_INDEX);
    }

    @Inject
    public IndexingTable(Provider<Definition> definition, Data data) {
        this.definition = definition.get();
        this.data = data;
        buildIndex();
    }

    @Override
    public void buildIndex() {
        /* populate the table of rules rewriting the top configuration */
        List<Index> indices = new ArrayList<Index>();
        indices.add(data.TOP_INDEX);
        indices.add(data.BOTTOM_INDEX);
        for (KLabelConstant kLabel : definition.kLabels()) {
            indices.add(new KLabelIndex(kLabel));
            indices.add(new FreezerIndex(kLabel, -1));
            if (!kLabel.productions().isEmpty()) {
                int maxArity = getMaxArityForProductions(kLabel.productions());
                for (int i = 0; i < maxArity; ++i) {
                    indices.add(new FreezerIndex(kLabel, i));
                }
            }
        }
        //for (KLabelConstant frozenKLabel : definition.frozenKLabels()) {
        //    for (int i = 0; i < frozenKLabel.productions().get(0).getArity(); ++i) {
        //        indices.add(new FreezerIndex(frozenKLabel, i));
        //    }
        //}
        for (Sort sort : definition.builtinSorts()) {
            indices.add(new TokenIndex(sort));
        }

        /* Map each index to a list of rules unifiable with that index */
        /* Heating rules and regular rules have their first index checked */
        /* Cooling rules have their second index checked */
        ImmutableMap.Builder<Index, List<Rule>> mapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> heatingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> coolingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> instreamMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> outstreamMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> simulationMapBuilder = ImmutableMap.builder();

        for (Index index : indices) {
            ImmutableList.Builder<Rule> listBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> heatingListBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> coolingListBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> instreamListBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> outstreamListBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> simulationListBuilder = ImmutableList.builder();

            for (Rule rule : definition.rules()) {
                if (rule.containsAttribute("heat")) {
                    if (index.isUnifiable(rule.indexingPair().first)) {
                        heatingListBuilder.add(rule);
                    }
                } else if (rule.containsAttribute("cool")) {
                    if (index.isUnifiable(rule.indexingPair().second)) {
                        coolingListBuilder.add(rule);
                    }
                } else if (rule.containsAttribute(Constants.STDIN)) {
                    if (index.isUnifiable(rule.indexingPair().second)) {
                        instreamListBuilder.add(rule);
                    }
                } else if (rule.containsAttribute(Constants.STDOUT) || rule.containsAttribute(Constants.STDERR)) {
                    if (index.isUnifiable(rule.indexingPair().first)) {
                        outstreamListBuilder.add(rule);
                    }
                } else if (rule.containsAttribute("alphaRule")){
                    if(index.isUnifiable(rule.indexingPair().first)) {
                        simulationListBuilder.add(rule);
                    }
                } else {
                    if (index.isUnifiable(rule.indexingPair().first)) {
                        listBuilder.add(rule);
                    }
                }
            }
            ImmutableList<Rule> rules = listBuilder.build();
            if (!rules.isEmpty()) {
                mapBuilder.put(index, rules);
            }
            rules = heatingListBuilder.build();
            if (!rules.isEmpty()) {
                heatingMapBuilder.put(index, rules);
            }
            rules = coolingListBuilder.build();
            if (!rules.isEmpty()) {
                coolingMapBuilder.put(index, rules);
            }
            rules = instreamListBuilder.build();
            if (!rules.isEmpty()) {
                instreamMapBuilder.put(index, rules);
            }
            rules = outstreamListBuilder.build();
            if (!rules.isEmpty()) {
                outstreamMapBuilder.put(index, rules);
            }
            rules = simulationListBuilder.build();
            if(!rules.isEmpty()){
                simulationMapBuilder.put(index, rules);
            }
        }
        heatingRuleTable = heatingMapBuilder.build();
        coolingRuleTable = coolingMapBuilder.build();
        instreamRuleTable = instreamMapBuilder.build();
        outstreamRuleTable = outstreamMapBuilder.build();
        ruleTable = mapBuilder.build();
        simulationRuleTable = simulationMapBuilder.build();

        ImmutableList.Builder<Rule> listBuilder = ImmutableList.builder();
        for (Rule rule : definition.rules()) {
            if (!rule.containsKCell() && !rule.containsAttribute(Constants.STDIN)
                        && !rule.containsAttribute(Constants.STDOUT)
                        && !rule.containsAttribute(Constants.STDERR)) {
                    listBuilder.add(rule);
            }
        }
        unindexedRules = listBuilder.build();
    }

    /**
     * This methos takes a list of productions with the same kLabel, and finds the maximum arity.
     * This is needed to avoid situations where there might be more productions with different
     * arities belonging to same label, for example:
     *
     *          syntax Foo ::= Bar "*" Bar [klabel(Foo)]
     *          syntax Foo ::= Bar "*" [klabel(Foo)]
     *
     * @param productions
     * @return
     */
    private int getMaxArityForProductions(List<Production> productions) {
        int max = productions.get(0).getArity();
        if (productions.size() > 1){
            for (Production production : productions.subList(1,productions.size())){
                if (production.getArity() > max){
                    max = production.getArity();
                }
            }
        }
        return max;
    }

    /**
     * Given a term, it uses queries the index table to find the rules that may apply.
     * @param term  The term being re-written
     * @return  A list of rules that may apply
     */
    @Override
    public List<Rule> getRules(Term term) {
        return getRulesFromCfgTermIdx(getConfigurationTermIndex(term));
    }

    @Override
    public List<Rule> getRules(List<Cell<?>> indexingCells) {
        return getRulesFromCfgTermIdx(getConfigurationTermIndex(indexingCells));
    }

    private List<Rule> getRulesFromCfgTermIdx(ConfigurationTermIndex cfgTermIdx) {
        Set<Rule> rules = new LinkedHashSet<>();

        /* give priority to IO rules */
        for (IndexingPair pair : cfgTermIdx.getInstreamIndexingPairs()) {
            if (instreamRuleTable.get(pair.second) != null) {
                for (Rule rule : instreamRuleTable.get(pair.second)) {
                    if (rule.lookups().equalities().size() <= cfgTermIdx.maxInputBufLen()) {
                        rules.add(rule);
                    }
                }
            }
        }

        for (IndexingPair pair : cfgTermIdx.getOutstreamIndexingPairs()) {
            if (outstreamRuleTable.get(pair.first) != null) {
                for (Rule rule : outstreamRuleTable.get(pair.first)) {
                    if (rule.lookups().equalities().size() <= cfgTermIdx.maxOutputBufLen()) {
                        rules.add(rule);
                    }
                }
            }
        }

        for (IndexingPair pair : cfgTermIdx.getKCellIndexingPairs()) {
            if (ruleTable.get(pair.first) != null) {
                rules.addAll(ruleTable.get(pair.first));
            }
            if (heatingRuleTable.get(pair.first) != null) {
                rules.addAll(heatingRuleTable.get(pair.first));
            }
            if (coolingRuleTable.get(pair.second) != null) {
                rules.addAll(coolingRuleTable.get(pair.second));
            }
        }

        rules.addAll(unindexedRules);

        return new ArrayList<>(rules);
    }

    private ConfigurationTermIndex getConfigurationTermIndex(List<Cell<?>> indexingCells) {
        List<IndexingPair> kCellIndexingPairs = new ArrayList<>();
        List<IndexingPair> instreamIndexingPairs = new ArrayList<>();
        List<IndexingPair> outstreamIndexingPairs = new ArrayList<>();
        int maxInputBufLen = 0;
        int maxOutputBufLen = 0;

        for (Cell<?> cell : indexingCells) {
            CellLabel cellLabel = cell.getLabel();
            String streamCellAttr = definition.context()
                    .getConfigurationStructureMap().get(cellLabel.name()).cell
                    .getCellAttribute(Attribute.STREAM_KEY);

            if (cellLabel.equals(CellLabel.K)) {
                kCellIndexingPairs.add(IndexingPair.getKCellIndexingPair(cell, definition));
            } else if (Constants.STDIN.equals(streamCellAttr)) {
                Term instream = cell.getContent();
                instreamIndexingPairs.add(IndexingPair.getInstreamIndexingPair(instream, definition));
                if (instream instanceof BuiltinList) {
                    maxInputBufLen = Math.max(maxInputBufLen, ((BuiltinList) instream).concreteSize());
                }
            } else if (Constants.STDOUT.equals(streamCellAttr) || Constants.STDERR.equals(streamCellAttr)) {
                Term outstream = cell.getContent();
                outstreamIndexingPairs.add(IndexingPair.getOutstreamIndexingPair(outstream, definition));
                if (outstream instanceof BuiltinList) {
                    maxOutputBufLen = Math.max(maxOutputBufLen, ((BuiltinList) outstream).concreteSize());
                }
            } else {
                assert false : "unexpected indexing cell " + cell;
            }
        }

        return new ConfigurationTermIndex(kCellIndexingPairs,
                instreamIndexingPairs, outstreamIndexingPairs,
                maxInputBufLen, maxOutputBufLen);
    }

    private ConfigurationTermIndex getConfigurationTermIndex(Term term) {
        return getConfigurationTermIndex(IndexingCellsCollector.getIndexingCells(term, definition));
    }

    public Map<Index, List<Rule>> getSimulationRuleTable() {
        return simulationRuleTable;
    }

}
