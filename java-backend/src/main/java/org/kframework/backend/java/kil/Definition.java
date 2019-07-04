// Copyright (c) 2013-2019 K Team. All Rights Reserved.
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
import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.symbolic.JavaBackend;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Module;
import org.kframework.kil.Attribute;
import org.kframework.kil.loader.Context;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.collection.JavaConversions;
import scala.collection.JavaConverters;

import javax.annotation.Nullable;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;

/**
 * A K definition in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Definition extends JavaSymbolicObject {

    private static class DefinitionData implements Serializable {
        public final Subsorts subsorts;
        public Map<String, DataStructureSort> dataStructureSorts;
        public final SetMultimap<String, SortSignature> signatures;
        public final ImmutableMap<String, Att> kLabelAttributes;
        public final Map<Sort, org.kframework.kore.KLabel> freshFunctionNames;
        public final Map<Sort, Sort> smtSortFlattening;
        public final Set<Sort> smtPreludeSorts;

        private DefinitionData(
                Subsorts subsorts,
                Map<String, DataStructureSort> dataStructureSorts,
                SetMultimap<String, SortSignature> signatures,
                ImmutableMap<String, Att> kLabelAttributes,
                Map<Sort, org.kframework.kore.KLabel> freshFunctionNames,
                Map<Sort, Sort> smtSortFlattening,
                Set<Sort> smtPreludeSorts) {
            this.subsorts = subsorts;
            this.dataStructureSorts = dataStructureSorts;
            this.signatures = signatures;
            this.kLabelAttributes = kLabelAttributes;
            this.freshFunctionNames = freshFunctionNames;
            this.smtSortFlattening = smtSortFlattening;
            this.smtPreludeSorts = smtPreludeSorts;
        }
    }

    private final List<Rule> rules = Lists.newArrayList();
    private final List<Rule> macros = Lists.newArrayList();
    private final List<Rule> specRules = new ArrayList<>();

    @SuppressWarnings("unused") //for debug
    public final List<Rule> specRulesPublic = Collections.unmodifiableList(specRules);
    private final Multimap<KLabelConstant, Rule> functionRules = ArrayListMultimap.create();
    private final Multimap<KLabelConstant, Rule> sortPredicateRules = HashMultimap.create();
    private final Multimap<KLabelConstant, Rule> anywhereRules = ArrayListMultimap.create();
    private final Multimap<KLabelConstant, Rule> patternRules = ArrayListMultimap.create();
    private final List<Rule> patternFoldingRules = new ArrayList<>();

    private final Set<KLabelConstant> kLabels = new LinkedHashSet<>();
    private final Set<KLabelConstant> kLabelsPublic = Collections.unmodifiableSet(kLabels);

    private DefinitionData definitionData;
    private transient Context context;

    private transient KExceptionManager kem;

    /**
     * the automaton rules used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
     */
    public Map<String, Rule> automatons = new HashMap<>();
    /**
     * all the rules indexed with the ordinal used by {@link org.kframework.backend.java.symbolic.FastRuleMatcher}
     */
    public Map<Integer, Rule> ruleTable;

    public final Map<Integer, Integer> reverseRuleTable = new HashMap<>();

    private final Map<KItem.CacheTableColKey, KItem.CacheTableValue> sortCacheTable = new HashMap<>();

    public Definition(org.kframework.definition.Module module, KExceptionManager kem) {
        this.kem = kem;

        Module moduleWithPolyProds = RuleGrammarGenerator.getCombinedGrammar(module, false).getExtensionModule();

        ImmutableSetMultimap.Builder<String, SortSignature> signaturesBuilder = ImmutableSetMultimap.builder();
        JavaConversions.mapAsJavaMap(moduleWithPolyProds.signatureFor()).entrySet().stream().forEach(e -> {
            JavaConversions.setAsJavaSet(e.getValue()).stream().forEach(p -> {
                ImmutableList.Builder<Sort> sortsBuilder = ImmutableList.builder();
                stream(p._1()).map(s -> Sort.of(s)).forEach(sortsBuilder::add);
                signaturesBuilder.put(
                        e.getKey().name(),
                        new SortSignature(sortsBuilder.build(), Sort.of(p._2())));
            });
        });

        ImmutableMap.Builder<String, Att> attributesBuilder = ImmutableMap.builder();
        JavaConversions.mapAsJavaMap(module.attributesFor()).entrySet().stream().forEach(e -> {
            attributesBuilder.put(e.getKey().name(), e.getValue());
        });

        definitionData = new DefinitionData(
                new Subsorts(moduleWithPolyProds),
                getDataStructureSorts(module),
                signaturesBuilder.build(),
                attributesBuilder.build(),
                JavaConverters.mapAsJavaMapConverter(module.freshFunctionFor()).asJava().entrySet().stream().collect(Collectors.toMap(
                        e -> Sort.of(e.getKey()),
                        e -> e.getValue())),
                Collections.emptyMap(),
                getSmtPreludeSorts(module)
        );
        context = null;

        this.ruleTable = new HashMap<>();
    }

    private Map<String, DataStructureSort> getDataStructureSorts(Module module) {
        ImmutableMap.Builder<String, DataStructureSort> builder = ImmutableMap.builder();
        for (org.kframework.definition.Production prod : iterable(module.productions())) {
            Optional<?> assoc = prod.att().getOptional(Attribute.ASSOCIATIVE_KEY);
            Optional<?> comm = prod.att().getOptional(Attribute.COMMUTATIVE_KEY);
            Optional<?> idem = prod.att().getOptional(Attribute.IDEMPOTENT_KEY);

            if (prod.sort().equals(Sorts.KList()) || prod.sort().equals(Sorts.KBott()))
                continue;
            if (assoc.isPresent() && !comm.isPresent() && !idem.isPresent()) {
                if (!prod.att().contains(Attribute.HOOK_KEY))
                    continue;
            } else if (assoc.isPresent() && comm.isPresent() && idem.isPresent()) {
            } else if (assoc.isPresent() && comm.isPresent() && !idem.isPresent()) {
                //TODO(dwightguth): distinguish between Bag and Map
                if (!prod.att().contains(Attribute.HOOK_KEY))
                    continue;
            } else if (!assoc.isPresent() && !comm.isPresent() && !idem.isPresent()) {
                continue;
            } else {
                throw KEMException.criticalError("Unexpected combination of assoc, comm, idem attributes found. Currently "
                        + "only sets, maps, and lists are supported: " + prod, prod);
            }
            DataStructureSort sort = new DataStructureSort(
                    prod.klabel().get(),
                    KLabel.parse(prod.att().<String>get("element")),
                    KLabel.parse(prod.att().<String>get(Attribute.UNIT_KEY)),
                    new HashMap<>());
            builder.put(prod.sort().toString(), sort);
        }
        return builder.build();
    }

    private Set<Sort> getSmtPreludeSorts(Module module) {
        ImmutableSet.Builder<Sort> builder = ImmutableSet.builder();
        for (org.kframework.definition.SyntaxSort decl : iterable(module.sortDeclarations())) {
            Optional<?> isSmtPreludeSort = decl.att().getOptional(Attribute.SMT_PRELUDE_KEY);
            if (isSmtPreludeSort.isPresent()) {
                builder.add(Sort.of(decl.sort()));
            }
        }
        return builder.build();
    }

    private static final Set<String> automatonAttributes
            = Sets.newHashSet(JavaBackend.MAIN_AUTOMATON, JavaBackend.SPEC_AUTOMATON);

    /**
     * Converts the org.kframework.Rules to backend Rules, also plugging in the automaton rule
     */
    public void addKoreRules(Module module, GlobalContext global) {
        KOREtoBackendKIL converter = new KOREtoBackendKIL(module, this, global, true);
        addKoreRules(module, converter, null, null);
    }

    public List<Rule> addKoreRules(Module module, KOREtoBackendKIL converter, @Nullable String filterAttribute,
                                   @Nullable UnaryOperator<Rule> rulePostProcessor) {
        //Add regular rules from all modules
        List<Rule> result = stream(module.rules())
                .filter(rule -> !containsAnyAttribute(rule, automatonAttributes))
                .filter(rule -> filterAttribute == null || rule.att().contains(filterAttribute))
                //Ensures that rule order in all collections remains the same across across different executions.
                .sorted(Comparator.comparingInt(rule -> rule.body().hashCode()))
                .map(rule -> addKoreRule(rule, converter, module, rulePostProcessor))
                .collect(Collectors.toList());

        //Add automaton from this module only
        stream(module.localRules())
                .filter(rule -> containsAnyAttribute(rule, automatonAttributes))
                .forEach(rule -> addKoreAutomaton(rule, converter, module));
        return result;
    }

    /**
     * @return the converted rule
     */
    public Rule addKoreRule(org.kframework.definition.Rule rule, KOREtoBackendKIL converter, Module module,
                            @Nullable UnaryOperator<Rule> rulePostProcessor) {
        Rule convertedRule = converter.convert(module, rule);
        if (rulePostProcessor != null) {
            convertedRule = rulePostProcessor.apply(convertedRule);
        }

        addRule(convertedRule);
        if (rule.att().contains(Att.topRule()) || rule.att().contains(Att.specification())) {
            reverseRuleTable.put(rule.hashCode(), reverseRuleTable.size());
            ruleTable.put(reverseRuleTable.get(rule.hashCode()), convertedRule);
        }
        return convertedRule;
    }

    /**
     * Automaton must be added after regular rules that it includes.
     */
    public void addKoreAutomaton(org.kframework.definition.Rule rule, KOREtoBackendKIL transformer, Module module) {
        Rule convertedRule = transformer.convert(module, rule);
        automatons.put(getFirstContainedAttribute(convertedRule, automatonAttributes), convertedRule);
    }

    public boolean containsAnyAttribute(org.kframework.definition.Rule rule, Set<String> attributeNames) {
        return attributeNames.stream().anyMatch(name -> rule.att().contains(name));
    }

    public String getFirstContainedAttribute(Rule rule, Set<String> attributeNames) {
        return attributeNames.stream().filter(name -> rule.att().contains(name)).findFirst().orElse(null);
    }

    public Definition(DefinitionData definitionData, KExceptionManager kem, Map<Integer, Rule> ruleTable,
                      Map<String, Rule> automatons) {
        this.kem = kem;
        this.ruleTable = ruleTable;
        this.automatons = automatons;

        this.definitionData = definitionData;
        this.context = null;
    }

    public void addKLabel(KLabelConstant kLabel) {
        kLabels.add(kLabel);
    }

    public void addKLabelCollection(Collection<KLabelConstant> kLabels) {
        for (KLabelConstant kLabel : kLabels) {
            addKLabel(kLabel);
        }
    }

    public void addRule(Rule rule) {
        if (rule.isFunction()) {
            functionRules.put(rule.definedKLabel(), rule);
            if (rule.isSortPredicate()) {
                sortPredicateRules.put((KLabelConstant) rule.sortPredicateArgument().kLabel(), rule);
            }
        } else if (rule.att().contains(Attribute.PATTERN_KEY)) {
            patternRules.put(rule.definedKLabel(), rule);
        } else if (rule.att().contains(Attribute.PATTERN_FOLDING_KEY)) {
            patternFoldingRules.add(rule);
        } else if (ExpandMacros.isMacro(rule)) {
            macros.add(rule);
        } else if (rule.att().contains(Attribute.ANYWHERE_KEY)) {
            if (!(rule.leftHandSide() instanceof KItem)) {
                kem.registerCriticalWarning(
                        "The Java backend only supports [anywhere] rule that rewrites KItem; but found:\n\t"
                                + rule, rule);
                return;
            }

            anywhereRules.put(rule.anywhereKLabel(), rule);
        } else {
            rules.add(rule);
            if (rule.att().contains(Att.specification())) {
                specRules.add(rule);
            }
        }
    }

    public void addRuleCollection(Collection<Rule> rules) {
        for (Rule rule : rules) {
            addRule(rule);
        }
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
        return kLabelsPublic;
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
    public JavaSymbolicObject accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
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

    public Map<String, Att> kLabelAttributes() {
        return definitionData.kLabelAttributes;
    }

    public Att kLabelAttributesOf(org.kframework.kore.KLabel label) {
        return Optional.ofNullable(definitionData.kLabelAttributes.get(label.name())).orElse(Att.empty());
    }

    public DataStructureSort dataStructureSortOf(Sort sort) {
        return definitionData.dataStructureSorts.get(sort.toString());
    }

    public Map<Sort, org.kframework.kore.KLabel> freshFunctionNames() {
        return definitionData.freshFunctionNames;
    }

    public Map<Sort, Sort> smtSortFlattening() {
        return definitionData.smtSortFlattening;
    }

    public Set<Sort> smtPreludeSorts() {
        return definitionData.smtPreludeSorts;
    }

    public DefinitionData definitionData() {
        return definitionData;
    }

    public Rule mainAutomaton() {
        return automatons.get(JavaBackend.MAIN_AUTOMATON);
    }

    public Rule specAutomaton() {
        return automatons.get(JavaBackend.SPEC_AUTOMATON);
    }
}
