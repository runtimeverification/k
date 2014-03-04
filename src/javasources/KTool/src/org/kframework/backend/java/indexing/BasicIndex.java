package org.kframework.backend.java.indexing;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.utils.general.IndexingStatistics;

import java.io.Serializable;
import java.util.Set;
import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.LinkedHashSet;

/**
 * The indexing scheme currently used in the Java Backend
 */
public class BasicIndex implements Serializable{
    private Map<Index, List<Rule>> ruleTable;
    private Map<Index, List<Rule>> heatingRuleTable;
    private Map<Index, List<Rule>> coolingRuleTable;
    private Map<Index, List<Rule>> simulationRuleTable;
    private List<Rule> unindexedRules;
    private final Definition definition;

    public BasicIndex(Definition definition) {
        this.definition = definition;
        buildBasicIndex();
    }

    private void buildBasicIndex() {

        /* populate the table of rules rewriting the top configuration */
        List<Index> indices = new ArrayList<Index>();
        indices.add(TopIndex.TOP);
        indices.add(BottomIndex.BOTTOM);
        for (KLabelConstant kLabel : definition.kLabels()) {
            indices.add(new KLabelIndex(kLabel));
            indices.add(new FreezerIndex(kLabel, -1));
            if (!kLabel.productions().isEmpty()) {
                for (int i = 0; i < kLabel.productions().get(0).getArity(); ++i) {
                    indices.add(new FreezerIndex(kLabel, i));
                }
            }
        }
        //for (KLabelConstant frozenKLabel : definition.frozenKLabels()) {
        //    for (int i = 0; i < frozenKLabel.productions().get(0).getArity(); ++i) {
        //        indices.add(new FreezerIndex(frozenKLabel, i));
        //    }
        //}
        for (String sort : definition.builtinSorts()) {
            indices.add(new TokenIndex(sort));
        }

        /* Map each index to a list of rules unifiable with that index */
        /* Heating rules and regular rules have their first index checked */
        /* Cooling rules have their second index checked */
        ImmutableMap.Builder<Index, List<Rule>> mapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> heatingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> coolingMapBuilder = ImmutableMap.builder();
        ImmutableMap.Builder<Index, List<Rule>> simulationMapBuilder = ImmutableMap.builder();

        for (Index index : indices) {
            ImmutableList.Builder<Rule> listBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> heatingListBuilder = ImmutableList.builder();
            ImmutableList.Builder<Rule> coolingListBuilder = ImmutableList.builder();
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
                } else if(rule.containsAttribute("alphaRule")){
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
            rules = simulationListBuilder.build();
            if(!rules.isEmpty()){
                simulationMapBuilder.put(index,rules);
            }
        }
        heatingRuleTable = heatingMapBuilder.build();
        coolingRuleTable = coolingMapBuilder.build();
        ruleTable = mapBuilder.build();
        simulationRuleTable = simulationMapBuilder.build();

        ImmutableList.Builder<Rule> listBuilder = ImmutableList.builder();
        for (Rule rule : definition.rules()) {
            if (!rule.containsKCell()) {
                listBuilder.add(rule);
            }
        }
        unindexedRules = listBuilder.build();
    }

    /**
     * Given a term, it uses queries the index table to find the rules that may apply.
     * @param term  The term being re-written
     * @return  A list of rules that may apply
     */
    public List<Rule> getRules(Term term) {
        Set<Rule> rules = new LinkedHashSet<>();

        for (IndexingPair pair : term.getIndexingPairs(definition)) {
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

    public Map<Index, List<Rule>> getSimulationRuleTable() {
        return simulationRuleTable;
    }
}
