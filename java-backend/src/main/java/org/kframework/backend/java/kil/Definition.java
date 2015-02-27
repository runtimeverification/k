// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ImmutableSetMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.SetMultimap;
import com.google.common.reflect.TypeToken;
import com.google.inject.name.Names;
import com.google.inject.Inject;


/**
 * A K definition in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Definition extends JavaSymbolicObject {

    private static class DefinitionData implements Serializable {
        public final Subsorts subsorts;
        public final Set<Sort> builtinSorts;
        public final Map<org.kframework.kil.Sort, DataStructureSort> dataStructureSorts;
        public final SetMultimap<String, SortSignature> signatures;
        public final ImmutableMap<String, Attributes> kLabelAttributes;
        public final Map<org.kframework.kil.Sort, String> freshFunctionNames;
        public final ConfigurationStructureMap configurationStructureMap;
        public transient GlobalOptions globalOptions;
        public transient KRunOptions kRunOptions;

        private DefinitionData(
                Subsorts subsorts,
                Set<Sort> builtinSorts,
                Map<org.kframework.kil.Sort, DataStructureSort> dataStructureSorts,
                SetMultimap<String, SortSignature> signatures,
                ImmutableMap<String, Attributes> kLabelAttributes,
                Map<org.kframework.kil.Sort, String> freshFunctionNames,
                ConfigurationStructureMap configurationStructureMap,
                GlobalOptions globalOptions,
                KRunOptions kRunOptions) {
            this.subsorts = subsorts;
            this.builtinSorts = builtinSorts;
            this.dataStructureSorts = dataStructureSorts;
            this.signatures = signatures;
            this.kLabelAttributes = kLabelAttributes;
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

    private final DefinitionData definitionData;
    private transient Context context;

    private transient KExceptionManager kem;

    private RuleIndex index;
    public final IndexingTable.Data indexingData;

    private final Map<KItem.CacheTableColKey, KItem.CacheTableValue> sortCacheTable = new HashMap<>();

    public Definition(Context context, KExceptionManager kem, IndexingTable.Data indexingData) {
        this.indexingData = indexingData;
        this.kem = kem;
        kLabels = new HashSet<>();
        frozenKLabels = new HashSet<>();

        ImmutableSet.Builder<Sort> builder = ImmutableSet.builder();
        // TODO(YilongL): this is confusing; give a better name to tokenSorts
        builder.addAll(Sort.of(context.getTokenSorts())); // e.g., [#String, #Int, Id, #Float]
        builder.addAll(TOKEN_SORTS); // [Bool, Int, Float, Char, String, List, Set, Map]

        ImmutableSetMultimap.Builder<String, SortSignature> signaturesBuilder = ImmutableSetMultimap.builder();
        for (Map.Entry<String, Production> entry : context.klabels.entries()) {
            ImmutableList.Builder<Sort> sortsBuilder = ImmutableList.builder();
            for (int i = 0; i < entry.getValue().getArity(); ++i) {
                sortsBuilder.add(Sort.of(entry.getValue().getChildSort(i)));
            }
            signaturesBuilder.put(
                    entry.getKey(),
                    new SortSignature(sortsBuilder.build(), Sort.of(entry.getValue().getSort())));
        }
        context.listKLabels.entries().stream().forEach(e -> {
            signaturesBuilder.put(
                    e.getKey(),
                    new SortSignature(ImmutableList.of(), Sort.of(e.getValue().getSort())));
        });

        ImmutableMap.Builder<String, Attributes> attributesBuilder = ImmutableMap.builder();
        for (Map.Entry<String, Collection<Production>> entry : context.klabels.asMap().entrySet()) {
            final Attributes attributes = new Attributes();
            entry.getValue().stream().filter(p -> !p.isLexical()).forEach(p -> {
                attributes.putAll(p.getAttributes());
                if (p.containsAttribute("binder")) {
                    attributes.add(new Attribute<>(
                            Attribute.Key.get(
                                    new TypeToken<Multimap<Integer, Integer>>() {},
                                    Names.named("binder")),
                            p.getBinderMap()));
                }
                if (p.containsAttribute("metabinder")) {
                    attributes.add(new Attribute<>(
                            Attribute.Key.get(
                                    new TypeToken<Multimap<Integer, Integer>>() {},
                                    Names.named("metabinder")),
                            p.getBinderMap()));
                }
            });
            // TODO(AndreiS): fix the definitions to pass this assertion
            //entry.getValue().stream().filter(p -> !p.isLexical()).forEach(p -> {
            //    assert p.getAttributes().equals(attributes) : "attribute mismatch:\n" + entry.getValue();
            //});
            attributesBuilder.put(entry.getKey(), attributes);
        }
        context.listKLabels.keySet().stream().forEach(key -> {
            attributesBuilder.put(key, new Attributes());
        });

        definitionData = new DefinitionData(
                new Subsorts(context),
                builder.build(),
                context.getDataStructureSorts(),
                signaturesBuilder.build(),
                attributesBuilder.build(),
                context.freshFunctionNames,
                context.getConfigurationStructureMap(),
                context.globalOptions,
                context.krunOptions);
        this.context = context;
    }

//    public Definition(org.kframework.definition.Module m) {
//        kLabels = new HashSet<>();
//        frozenKLabels = new HashSet<>();
//        definitionData = new DefinitionData(
//                new Subsorts(context),
//                ImmutableSet.builder()
//                        .addAll(TOKEN_SORTS)
//                        .add(Sort.of("#Int"))
//                        .add(Sort.of("#String"))
//                        .add(Sort.of("#Id"))
//                        .build(),
//                null,
//                context.klabels,
//                null,
//                null,
//                null,
//                context.globalOptions,
//                context.krunOptions);
//        this.indexingData = null;
//        this.kem = null;
//    }

    @Inject
    public Definition(DefinitionData definitionData, KExceptionManager kem, IndexingTable.Data indexingData) {
        this.indexingData = indexingData;
        this.kem = kem;
        kLabels = new HashSet<>();
        frozenKLabels = new HashSet<>();

        this.definitionData = definitionData;
        this.context = null;
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

    public Context context() {
        return context;
    }

    public void setContext(Context context) {
        this.context = context;
    }

    public GlobalOptions globalOptions() {
        return definitionData.globalOptions;
    }

    public void setGlobalOptions(GlobalOptions globalOptions) {
        this.definitionData.globalOptions = globalOptions;
    }

    public KRunOptions kRunOptions() {
        return definitionData.kRunOptions;
    }

    public void setKRunOptions(KRunOptions kRunOptions) {
        this.definitionData.kRunOptions = kRunOptions;
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
    public Set<SortSignature> signaturesOf(String label) {
        return definitionData.signatures.get(label);
    }

    public Map<String, Attributes> kLabelAttributes() {
        return definitionData.kLabelAttributes;
    }

    public Attributes kLabelAttributesOf(String label) {
        return Optional.ofNullable(definitionData.kLabelAttributes.get(label)).orElse(new Attributes());
    }

    public ConfigurationStructureMap getConfigurationStructureMap() {
        return definitionData.configurationStructureMap;
    }

    public DataStructureSort dataStructureSortOf(Sort sort) {
        return definitionData.dataStructureSorts.get(sort.toFrontEnd());
    }

    public Map<org.kframework.kil.Sort, String> freshFunctionNames() {
        return definitionData.freshFunctionNames;
    }

    public DefinitionData definitionData() {
        return definitionData;
    }

}
