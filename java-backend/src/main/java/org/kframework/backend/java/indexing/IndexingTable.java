// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.Provider;
import com.google.inject.Singleton;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.RuleAuditing;
import org.kframework.kil.Attribute;
import org.kframework.kil.loader.Constants;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;

/**
 * The indexing scheme currently used in the Java Backend
 */
public class IndexingTable implements Serializable, RuleIndex {

    private Map<Index, ImmutableSet<Rule>> ruleTable;
    private Map<Index, ImmutableSet<Rule>> heatingRuleTable;
    private Map<Index, ImmutableSet<Rule>> coolingRuleTable;
    private Map<Index, ImmutableSet<Rule>> instreamRuleTable;
    private Map<Index, ImmutableSet<Rule>> outstreamRuleTable;
    private ImmutableSet<Rule> unindexedRules;
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
        Set<Index> indices = new HashSet<Index>();
        indices.add(data.TOP_INDEX);
        indices.add(data.BOTTOM_INDEX);
        for (Rule rule : definition.rules()) {
            addFreezerIndices(indices, rule.indexingPair().first);
            addFreezerIndices(indices, rule.indexingPair().second);
        }
        for (KLabelConstant kLabel : definition.kLabels()) {
            indices.add(new KLabelIndex(kLabel));
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
        ImmutableMap.Builder<Index, ImmutableSet<Rule>> mapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, ImmutableSet<Rule>> heatingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, ImmutableSet<Rule>> coolingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, ImmutableSet<Rule>> instreamMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, ImmutableSet<Rule>> outstreamMapBuilder = ImmutableMap.builder();

        for (Index index : indices) {
            ImmutableSet.Builder<Rule> rulesBuilder = ImmutableSet.builder();
            ImmutableSet.Builder<Rule> heatingRulesBuilder = ImmutableSet.builder();
            ImmutableSet.Builder<Rule> coolingRulesBuilder = ImmutableSet.builder();
            ImmutableSet.Builder<Rule> instreamRulesBuilder = ImmutableSet.builder();
            ImmutableSet.Builder<Rule> outstreamRulesBuilder = ImmutableSet.builder();

            for (Rule rule : definition.rules()) {
                if (rule.containsAttribute("heat")) {
                    if (index.isUnifiable(rule.indexingPair().first)) {
                        heatingRulesBuilder.add(rule);
                    }
                } else if (rule.containsAttribute("cool")) {
                    if (index.isUnifiable(rule.indexingPair().second)) {
                        coolingRulesBuilder.add(rule);
                    }
                } else if (rule.containsAttribute(Constants.STDIN)) {
                    if (index.isUnifiable(rule.indexingPair().second)) {
                        instreamRulesBuilder.add(rule);
                    }
                } else if (rule.containsAttribute(Constants.STDOUT) || rule.containsAttribute(Constants.STDERR)) {
                    if (index.isUnifiable(rule.indexingPair().first)) {
                        outstreamRulesBuilder.add(rule);
                    }
                } else {
                    if (index.isUnifiable(rule.indexingPair().first)) {
                        rulesBuilder.add(rule);
                    }
                }
            }
            ImmutableSet<Rule> rules = rulesBuilder.build();
            if (!rules.isEmpty()) {
                mapBuilder.put(index, rules);
            }
            rules = heatingRulesBuilder.build();
            if (!rules.isEmpty()) {
                heatingMapBuilder.put(index, rules);
            }
            rules = coolingRulesBuilder.build();
            if (!rules.isEmpty()) {
                coolingMapBuilder.put(index, rules);
            }
            rules = instreamRulesBuilder.build();
            if (!rules.isEmpty()) {
                instreamMapBuilder.put(index, rules);
            }
            rules = outstreamRulesBuilder.build();
            if (!rules.isEmpty()) {
                outstreamMapBuilder.put(index, rules);
            }
        }
        heatingRuleTable = heatingMapBuilder.build();
        coolingRuleTable = coolingMapBuilder.build();
        instreamRuleTable = instreamMapBuilder.build();
        outstreamRuleTable = outstreamMapBuilder.build();
        ruleTable = mapBuilder.build();

        ImmutableSet.Builder<Rule> unindexedRulesBuilder = ImmutableSet.builder();
        for (Rule rule : definition.rules()) {
            if (!rule.containsKCell() && !rule.containsAttribute(Constants.STDIN)
                        && !rule.containsAttribute(Constants.STDOUT)
                        && !rule.containsAttribute(Constants.STDERR)) {
                    unindexedRulesBuilder.add(rule);
            }
        }
        unindexedRules = unindexedRulesBuilder.build();
    }

    private void addFreezerIndices(Set<Index> indices, Index index) {
        if (index instanceof FreezerIndex) {
            KLabelConstant kLabel = ((FreezerIndex) index).getKLabel();
            indices.add(new FreezerIndex(kLabel, -1));
            indices.add(index);
        }
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
    public List<Rule> getRules(List<CellCollection.Cell> indexingCells) {
        return getRulesFromCfgTermIdx(getConfigurationTermIndex(indexingCells));
    }

    private List<Rule> getRulesFromCfgTermIdx(ConfigurationTermIndex cfgTermIdx) {
        List<Rule> rules = Lists.newArrayList();

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

        if (!RuleAuditing.isAuditBegun() && RuleAuditing.isAudit()
                && !rules.contains(RuleAuditing.getAuditingRule())
                && !definition.functionRules().containsValue(RuleAuditing.getAuditingRule())) {
            StringBuilder message = new StringBuilder();
            for (IndexingPair pair : cfgTermIdx.getInstreamIndexingPairs()) {
                message.append("Could not find rule matching stdin cell index ");
                message.append(pair);
                message.append("\n");
            }
            for (IndexingPair pair : cfgTermIdx.getOutstreamIndexingPairs()) {
                message.append("Could not find rule matching stdout/stderr cell index ");
                message.append(pair);
                message.append("\n");
            }
            for (IndexingPair pair : cfgTermIdx.getKCellIndexingPairs()) {
                message.append("Could not find rule matching K cell index ");
                message.append(pair);
                message.append("\n");
            }
            throw RuleAuditing.fail(message.toString());
        }

        return rules;
    }

    private ConfigurationTermIndex getConfigurationTermIndex(List<CellCollection.Cell> indexingCells) {
        List<IndexingPair> kCellIndexingPairs = new ArrayList<>();
        List<IndexingPair> instreamIndexingPairs = new ArrayList<>();
        List<IndexingPair> outstreamIndexingPairs = new ArrayList<>();
        int maxInputBufLen = 0;
        int maxOutputBufLen = 0;

        for (CellCollection.Cell cell : indexingCells) {
            CellLabel cellLabel = cell.cellLabel();
            String streamCellAttr = definition.context()
                    .getConfigurationStructureMap().get(cellLabel.name()).cell
                    .getCellAttribute(Attribute.STREAM_KEY);

            if (cellLabel.equals(CellLabel.K)) {
                kCellIndexingPairs.add(IndexingPair.getKCellIndexingPair(cell.content(), definition));
            } else if (Constants.STDIN.equals(streamCellAttr)) {
                Term instream = cell.content();
                instreamIndexingPairs.add(IndexingPair.getInstreamIndexingPair(instream, definition));
                if (instream instanceof BuiltinList) {
                    maxInputBufLen = Math.max(maxInputBufLen, ((BuiltinList) instream).concreteSize());
                }
            } else if (Constants.STDOUT.equals(streamCellAttr) || Constants.STDERR.equals(streamCellAttr)) {
                Term outstream = cell.content();
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

}
