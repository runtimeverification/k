// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

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
import com.google.inject.Inject;
import com.google.inject.name.Names;
import org.kframework.attributes.Att;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.definition.Module;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.kore.convertors.KOREtoKIL;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.collection.JavaConversions;
import scala.collection.JavaConverters;

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
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.Sort;
import static org.kframework.Collections.*;

/**
 * A K definition in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Definition extends JavaSymbolicObject {

    public static final String AUTOMATON = "automaton";

    private static class DefinitionData implements Serializable {
        public final Subsorts subsorts;
        public final Set<Sort> builtinSorts;
        public final Map<org.kframework.kore.Sort, DataStructureSort> dataStructureSorts;
        public final SetMultimap<String, SortSignature> signatures;
        public final ImmutableMap<String, Attributes> kLabelAttributes;
        public final Map<Sort, String> freshFunctionNames;
        public final Map<Sort, Sort> smtSortFlattening;
        public final Map<CellLabel, ConfigurationInfo.Multiplicity> cellLabelMultiplicity;
        public final ConfigurationInfo configurationInfo;
        public final ConfigurationStructureMap configurationStructureMap;

        private DefinitionData(
                Subsorts subsorts,
                Set<Sort> builtinSorts,
                Map<org.kframework.kore.Sort, DataStructureSort> dataStructureSorts,
                SetMultimap<String, SortSignature> signatures,
                ImmutableMap<String, Attributes> kLabelAttributes,
                Map<Sort, String> freshFunctionNames,
                Map<Sort, Sort> smtSortFlattening,
                Map<CellLabel, ConfigurationInfo.Multiplicity> cellLabelMultiplicity,
                ConfigurationInfo configurationInfo,
                ConfigurationStructureMap configurationStructureMap) {
            this.subsorts = subsorts;
            this.builtinSorts = builtinSorts;
            this.dataStructureSorts = dataStructureSorts;
            this.signatures = signatures;
            this.kLabelAttributes = kLabelAttributes;
            this.freshFunctionNames = freshFunctionNames;
            this.smtSortFlattening = smtSortFlattening;
            this.cellLabelMultiplicity = cellLabelMultiplicity;
            this.configurationInfo = configurationInfo;
            this.configurationStructureMap = configurationStructureMap;
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

    private final DefinitionData definitionData;
    private transient Context context;

    private transient KExceptionManager kem;

    private RuleIndex index;
    public final IndexingTable.Data indexingData;

    // new indexing data
    /**
     * the automaton rule used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
     */
    public Rule automaton = null;
    /**
     * all the rules indexed with the ordinal used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
     */
    public final Map<Integer, Rule> ruleTable;

    public final Map<Integer, Integer> reverseRuleTable = new HashMap<>();

    private final Map<KItem.CacheTableColKey, KItem.CacheTableValue> sortCacheTable = new HashMap<>();

    public Definition(Context context, KExceptionManager kem, IndexingTable.Data indexingData) {
        kLabels = new HashSet<>();
        this.kem = kem;
        this.indexingData = indexingData;

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
                                    new TypeToken<Multimap<Integer, Integer>>() {
                                    },
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
                context.getDataStructureSorts().entrySet().stream().collect(Collectors.toMap(e -> Sort(e.getKey().getName()), Map.Entry::getValue)),
                signaturesBuilder.build(),
                attributesBuilder.build(),
                context.freshFunctionNames.entrySet().stream().collect(Collectors.toMap(e -> Sort.of(e.getKey()), Map.Entry::getValue)),
                context.smtSortFlattening.entrySet().stream().collect(Collectors.toMap(e -> Sort.of(e.getKey()), e -> Sort.of(e.getValue()))),
                context.getConfigurationStructureMap().entrySet().stream().collect(Collectors.toMap(
                        e -> CellLabel.of(e.getKey()),
                        e -> KOREtoBackendKIL.kil2koreMultiplicity(e.getValue().multiplicity))),
                null,
                context.getConfigurationStructureMap());
        this.context = context;
        this.ruleTable = new HashMap<>();
    }

    public Definition(org.kframework.definition.Module module, KExceptionManager kem) {
        kLabels = new HashSet<>();
        this.kem = kem;

        ImmutableSetMultimap.Builder<String, SortSignature> signaturesBuilder = ImmutableSetMultimap.builder();
        JavaConversions.mapAsJavaMap(module.signatureFor()).entrySet().stream().forEach(e -> {
            JavaConversions.setAsJavaSet(e.getValue()).stream().forEach(p -> {
                ImmutableList.Builder<Sort> sortsBuilder = ImmutableList.builder();
                JavaConversions.seqAsJavaList(p._1()).stream()
                        .map(s -> Sort.of(s.name()))
                        .forEach(sortsBuilder::add);
                signaturesBuilder.put(
                        e.getKey().name(),
                        new SortSignature(sortsBuilder.build(), Sort.of(p._2().name())));
            });
        });

        ImmutableMap.Builder<String, Attributes> attributesBuilder = ImmutableMap.builder();
        JavaConversions.mapAsJavaMap(module.attributesFor()).entrySet().stream().forEach(e -> {
            attributesBuilder.put(e.getKey().name(), new KOREtoKIL().convertAttributes(e.getValue()));
        });

        ConfigurationInfo configurationInfo = new ConfigurationInfoFromModule(module);

        definitionData = new DefinitionData(
                new Subsorts(module),
                ImmutableSet.<Sort>builder()
                        .addAll(TOKEN_SORTS)
                        .add(Sort.of("#Int"))
                        .add(Sort.of("#String"))
                        .add(Sort.of("#Id"))
                        .build(),
                getDataStructureSorts(module),
                signaturesBuilder.build(),
                attributesBuilder.build(),
                JavaConverters.mapAsJavaMapConverter(module.freshFunctionFor()).asJava().entrySet().stream().collect(Collectors.toMap(
                        e -> Sort.of(e.getKey().name()),
                        e -> e.getValue().name())),
                Collections.emptyMap(),
                configurationInfo.getCellSorts().stream().collect(Collectors.toMap(
                        s -> CellLabel.of(configurationInfo.getCellLabel(s).name()),
                        configurationInfo::getMultiplicity)),
                configurationInfo,
                null);
        context = null;

        this.indexingData = new IndexingTable.Data();
        this.ruleTable = new HashMap<>();
    }

    private Map<org.kframework.kore.Sort, DataStructureSort> getDataStructureSorts(Module module) {
        ImmutableMap.Builder<org.kframework.kore.Sort, DataStructureSort> builder = ImmutableMap.builder();
        for (org.kframework.definition.Production prod : iterable(module.productions())) {
            Optional<?> assoc = prod.att().getOptional(Attribute.ASSOCIATIVE_KEY);
            Optional<?> comm = prod.att().getOptional(Attribute.COMMUTATIVE_KEY);
            Optional<?> idem = prod.att().getOptional(Attribute.IDEMPOTENT_KEY);

            org.kframework.kil.Sort type;
            if (prod.sort().equals(Sorts.KList()) || prod.sort().equals(Sorts.KBott()))
                continue;
            if (assoc.isPresent() && !comm.isPresent() && !idem.isPresent()) {
                type = org.kframework.kil.Sort.LIST;
            } else if (assoc.isPresent() && comm.isPresent() && idem.isPresent()) {
                type = org.kframework.kil.Sort.SET;
            } else if (assoc.isPresent() && comm.isPresent() && !idem.isPresent()) {
                //TODO(dwightguth): distinguish between Bag and Map
                if (!prod.att().contains(Attribute.HOOK_KEY))
                    continue;
                type = org.kframework.kil.Sort.MAP;
            } else if (!assoc.isPresent() && !comm.isPresent() && !idem.isPresent()) {
                continue;
            } else {
                throw KEMException.criticalError("Unexpected combination of assoc, comm, idem attributes found. Currently "
                        + "only sets, maps, and lists are supported: " + prod, prod);
            }
            DataStructureSort sort = new DataStructureSort(prod.sort().name(), type,
                    prod.klabel().get().name(),
                    prod.att().<String>get("element").get(),
                    prod.att().<String>get(Attribute.UNIT_KEY).get(),
                    new HashMap<>());
            builder.put(prod.sort(), sort);
        }
        return builder.build();
    }

    /**
     * Converts the org.kframework.Rules to backend Rules, also plugging in the automaton rule
     */
    public void addKoreRules(Module module, GlobalContext global) {
        KOREtoBackendKIL transformer = new KOREtoBackendKIL(module, this, global, false, global.krunOptions.experimental.prove != null);
        List<org.kframework.definition.Rule> koreRules = JavaConversions.setAsJavaSet(module.sentences()).stream()
                .filter(org.kframework.definition.Rule.class::isInstance)
                .map(org.kframework.definition.Rule.class::cast)
                .collect(Collectors.toList());
        koreRules.forEach(r -> {
            if (r.att().contains(Att.topRule())) {
//            if (r.body() instanceof KApply && ((KApply) r.body()).klabel().name().equals(KLabels.GENERATED_TOP_CELL)) {
                if (!r.att().contains(AUTOMATON)) {
                    reverseRuleTable.put(r.hashCode(), reverseRuleTable.size());
                }
            }
        });
        koreRules.forEach(r -> {
            Rule convertedRule = transformer.convert(Optional.of(module), r);
            addRule(convertedRule);
//            if (r.body() instanceof KApply && ((KApply) r.body()).klabel().name().equals(KLabels.GENERATED_TOP_CELL)) {
            if (r.att().contains(Att.topRule())) {
                if (!r.att().contains(AUTOMATON)) {
                    ruleTable.put(reverseRuleTable.get(r.hashCode()), convertedRule);
                }
            }
            if (r.att().contains(AUTOMATON)) {
                automaton = convertedRule;
            }
        });
    }

    @Inject
    public Definition(DefinitionData definitionData, KExceptionManager kem, IndexingTable.Data indexingData) {
        this(definitionData, kem, indexingData, new HashMap<>(), null);
    }

    public Definition(DefinitionData definitionData, KExceptionManager kem, IndexingTable.Data indexingData, Map<Integer, Rule> ruleTable, Rule automaton) {
        kLabels = new HashSet<>();
        this.kem = kem;
        this.indexingData = indexingData;
        this.ruleTable = ruleTable;
        this.automaton = automaton;

        this.definitionData = definitionData;
        this.context = null;
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

    public KItem.CacheTableValue getSortCacheValue(KItem.CacheTableColKey key) {
        synchronized (sortCacheTable) {
            return sortCacheTable.get(key);
        }
    }

    public void putSortCacheValue(KItem.CacheTableColKey key, KItem.CacheTableValue value) {
        synchronized (sortCacheTable) {
            sortCacheTable.put(key, value);
        }
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
        return definitionData.dataStructureSorts.get(Sort(sort.name()));
    }

    public Map<Sort, String> freshFunctionNames() {
        return definitionData.freshFunctionNames;
    }

    public Map<Sort, Sort> smtSortFlattening() {
        return definitionData.smtSortFlattening;
    }

    public ConfigurationInfo.Multiplicity cellMultiplicity(CellLabel label) {
        return definitionData.cellLabelMultiplicity.get(label);
    }

    public ConfigurationInfo configurationInfo() {
        return definitionData.configurationInfo;
    }

    public DefinitionData definitionData() {
        return definitionData;
    }

}
