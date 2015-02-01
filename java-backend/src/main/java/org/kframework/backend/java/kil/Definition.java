// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.SetMultimap;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.inject.Inject;


/**
 * A K definition in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Definition extends JavaSymbolicObject {

    private static class DefinitionData {
        public final Subsorts subsorts;
        public final Set<Sort> builtinSorts;
        public final Map<org.kframework.kil.Sort, DataStructureSort> dataStructureSorts;
        public final SetMultimap<String, Production> productions;
        public final SetMultimap<String, Production> listKLabels;
        public final Map<org.kframework.kil.Sort, String> freshFunctionNames;
        public final ConfigurationStructureMap configurationStructureMap;
        public final GlobalOptions globalOptions;
        public final KRunOptions kRunOptions;

        private DefinitionData(
                Subsorts subsorts,
                Set<Sort> builtinSorts,
                Map<org.kframework.kil.Sort, DataStructureSort> dataStructureSorts,
                SetMultimap<String, Production> productions,
                SetMultimap<String, Production> listKLabels,
                Map<org.kframework.kil.Sort, String> freshFunctionNames,
                ConfigurationStructureMap configurationStructureMap,
                GlobalOptions globalOptions,
                KRunOptions kRunOptions) {
            this.subsorts = subsorts;
            this.builtinSorts = builtinSorts;
            this.dataStructureSorts = dataStructureSorts;
            this.productions = productions;
            this.listKLabels = listKLabels;
            this.freshFunctionNames = freshFunctionNames;
            this.configurationStructureMap = configurationStructureMap;
            this.globalOptions = globalOptions;
            this.kRunOptions = kRunOptions;
        }
    }

    public static final Set<Sort> TOKEN_SORTS = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.FLOAT,
            Sort.CHAR,
            Sort.STRING,
            Sort.LIST,
            Sort.SET,
            Sort.MAP);

    private final List<Rule> rules = Lists.newArrayList();
    private final List<Rule> macros = Lists.newArrayList();
    private final Multimap<KLabelConstant, Rule> functionRules = ArrayListMultimap.create();
    private final Multimap<KLabelConstant, Rule> sortPredicateRules = HashMultimap.create();
    private final Multimap<KLabelConstant, Rule> anywhereRules = HashMultimap.create();
    private final Multimap<KLabelConstant, Rule> patternRules = ArrayListMultimap.create();
    private final List<Rule> patternFoldingRules = new ArrayList<>();

    private final Set<KLabelConstant> kLabels;
    private final Set<KLabelConstant> frozenKLabels;

    private final transient DefinitionData definitionData;

    private transient KExceptionManager kem;

    private RuleIndex index;
    public final IndexingTable.Data indexingData;

    private final Map<KItem.CacheTableColKey, KItem.CacheTableValue> sortCacheTable = new HashMap<>();

    @Inject
    public Definition(Context context, KExceptionManager kem, IndexingTable.Data indexingData) {
        this.indexingData = indexingData;
        this.kem = kem;
        kLabels = new HashSet<>();
        frozenKLabels = new HashSet<>();

        ImmutableSet.Builder<Sort> builder = ImmutableSet.builder();
        // TODO(YilongL): this is confusing; give a better name to tokenSorts
        builder.addAll(Sort.of(context.getTokenSorts())); // e.g., [#String, #Int, Id, #Float]
        builder.addAll(TOKEN_SORTS); // [Bool, Int, Float, Char, String, List, Set, Map]

        definitionData = new DefinitionData(
                new Subsorts(context),
                builder.build(),
                context.getDataStructureSorts(),
                context.klabels,
                context.listKLabels,
                context.freshFunctionNames,
                context.getConfigurationStructureMap(),
                context.globalOptions,
                context.krunOptions);
    }

//    public Definition(org.kframework.definition.Module m) {
//        kLabels = new HashSet<>();
//        frozenKLabels = new HashSet<>();
//
//        ImmutableSet.Builder<Sort> builder = ImmutableSet.builder();
//        // TODO(YilongL): this is confusing; give a better name to tokenSorts
//        builder.addAll(Sort.of(context.getTokenSorts())); // e.g., [#String, #Int, Id, #Float]
//        builder.addAll(TOKEN_SORTS); // [Bool, Int, Float, Char, String, List, Set, Map]
//
//        definitionData = new DefinitionData(
//                new Subsorts(context),
//                builder.build(),
//                context.getDataStructureSorts(),
//                context.klabels,
//                context.listKLabels,
//                context.freshFunctionNames,
//                context.getConfigurationStructureMap(),
//                context.globalOptions,
//                context.krunOptions);
//    }

    @Inject
    public Definition(DefinitionData definitionData, KExceptionManager kem, IndexingTable.Data indexingData) {
        this.indexingData = indexingData;
        this.kem = kem;
        kLabels = new HashSet<>();
        frozenKLabels = new HashSet<>();

        this.definitionData = definitionData;
    }

    public void addFrozenKLabel(KLabelConstant frozenKLabel) {
        frozenKLabels.add(frozenKLabel);
    }

    public void addFrozenKLabelCollection(Collection<KLabelConstant> frozenKLabels) {
        for (KLabelConstant frozenKLabel : frozenKLabels) {
            this.frozenKLabels.add(frozenKLabel);
        }
    }

    public void addKLabel(KLabelConstant kLabel) {
        kLabels.add(kLabel);
    }

    public void addKLabelCollection(Collection<KLabelConstant> kLabels) {
        for (KLabelConstant kLabel : kLabels) {
            this.kLabels.add(kLabel);
        }
    }

    public void addRule(Rule rule) {
        if (rule.isFunction()) {
            functionRules.put(rule.definedKLabel(), rule);
            if (rule.isSortPredicate()) {
                sortPredicateRules.put((KLabelConstant) rule.sortPredicateArgument().kLabel(), rule);
            }
        } else if (rule.containsAttribute(Attribute.PATTERN_KEY)) {
            patternRules.put(rule.definedKLabel(), rule);
        } else if (rule.containsAttribute(Attribute.PATTERN_FOLDING_KEY)) {
            patternFoldingRules.add(rule);
        } else if (rule.containsAttribute(Attribute.MACRO_KEY)) {
            macros.add(rule);
        } else if (rule.containsAttribute(Attribute.ANYWHERE_KEY)) {
            if (!(rule.leftHandSide() instanceof KItem)) {
                kem.registerCriticalWarning(
                        "The Java backend only supports [anywhere] rule that rewrites KItem; but found:\n\t"
                                + rule, rule);
                return;
            }

            anywhereRules.put(rule.anywhereKLabel(), rule);
        } else {
            rules.add(rule);
        }
    }

    public void addRuleCollection(Collection<Rule> rules) {
        for (Rule rule : rules) {
            addRule(rule);
        }
    }

    /**
     * TODO(YilongL): this name is really confusing; looks like it's only used
     * in building index;
     */
    public Set<Sort> builtinSorts() {
        return definitionData.builtinSorts;
    }

    public Set<Sort> allSorts() {
        return definitionData.subsorts.allSorts();
    }

    public Subsorts subsorts() {
        return definitionData.subsorts;
    }

    public void setContext(Context context) {
    }

    public void setKem(KExceptionManager kem) {
        this.kem = kem;
    }

    public Multimap<KLabelConstant, Rule> functionRules() {
        return functionRules;
    }

    public Multimap<KLabelConstant, Rule> anywhereRules() {
        return anywhereRules;
    }

    public Collection<Rule> sortPredicateRulesOn(KLabelConstant kLabel) {
        if (sortPredicateRules.isEmpty()) {
            return Collections.emptyList();
        }
        return sortPredicateRules.get(kLabel);
    }

    public Multimap<KLabelConstant, Rule> patternRules() {
        return patternRules;
    }

    public List<Rule> patternFoldingRules() {
        return patternFoldingRules;
    }

    public Set<KLabelConstant> frozenKLabels() {
        return frozenKLabels;
    }

    public Set<KLabelConstant> kLabels() {
        return Collections.unmodifiableSet(kLabels);
    }

    public List<Rule> macros() {
        // TODO(AndreiS): fix this issue with modifiable collections
        //return Collections.unmodifiableList(macros);
        return macros;
    }

    public List<Rule> rules() {
        // TODO(AndreiS): fix this issue with modifiable collections
        //return Collections.unmodifiableList(rules);
        return rules;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

    public void setIndex(RuleIndex index) {
        this.index = index;
    }

    public RuleIndex getIndex() {
        return index;
    }

    public Map<KItem.CacheTableColKey, KItem.CacheTableValue> getSortCacheTable() {
        return sortCacheTable;
    }

    // added from context
    public Set<Production> productionsOf(String label) {
        return definitionData.productions.get(label);
    }

    public Collection<Production> productions() {
        return definitionData.productions.values();
    }

    public Set<Production> listLabelsOf(String label) {
        return definitionData.listKLabels.get(label);
    }

    public ConfigurationStructureMap getConfigurationStructureMap() {
        return definitionData.configurationStructureMap;
    }

    public DataStructureSort dataStructureSortOf(Sort sort) {
        return definitionData.dataStructureSorts.get(sort.toFrontEnd());
    }

    public GlobalOptions globalOptions() {
        return definitionData.globalOptions;
    }

    public KRunOptions kRunOptions() {
        return definitionData.kRunOptions;
    }

    public Map<org.kframework.kil.Sort, String> freshFunctionNames() {
        return definitionData.freshFunctionNames;
    }

    public DefinitionData definitionData() {
        return definitionData;
    }

}
