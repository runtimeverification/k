// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.indexing.RuleIndex;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Subsorts;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.loader.Context;
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
import com.google.common.collect.Multimap;
import com.google.inject.Inject;


/**
 * A K definition in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Definition extends JavaSymbolicObject {

    public static final Set<Sort> TOKEN_SORTS = ImmutableSet.of(
            Sort.BOOL,
            Sort.INT,
            Sort.FLOAT,
            Sort.CHAR,
            Sort.STRING,
            Sort.LIST,
            Sort.SET,
            Sort.MAP);

    private final List<Rule> rules;
    private final List<Rule> macros;
    private final Multimap<KLabelConstant, Rule> functionRules = ArrayListMultimap.create();
    private final Multimap<KLabelConstant, Rule> sortPredicateRules = HashMultimap.create();
    private final Multimap<KLabelConstant, Rule> anywhereRules = HashMultimap.create();
    private final Multimap<KLabelConstant, Rule> patternRules = ArrayListMultimap.create();
    private final List<Rule> patternFoldingRules = new ArrayList<>();
    private final Set<KLabelConstant> kLabels;
    private final Set<KLabelConstant> frozenKLabels;
    private transient Context context;
    private transient KExceptionManager kem;
    private final Subsorts subsorts;
    private final Set<Sort> tokenSorts;
    private final Set<Sort> builtinSorts;
    private RuleIndex index;
    public final IndexingTable.Data indexingData;

    private final Map<KItem.CacheTableColKey, KItem.CacheTableValue> sortCacheTable = new HashMap<>();

    @Inject
    public Definition(Context context, KExceptionManager kem, IndexingTable.Data indexingData) {
        this.context = context;
        this.indexingData = indexingData;
        this.kem = kem;
        rules = new ArrayList<>();
        macros = new ArrayList<>();
        kLabels = new HashSet<>();
        frozenKLabels = new HashSet<>();

        subsorts = new Subsorts(context);
        tokenSorts = Sort.of(context.getTokenSorts());

        ImmutableSet.Builder<Sort> builder = ImmutableSet.builder();
        // TODO(YilongL): this is confusing; give a better name to tokenSorts
        builder.addAll(tokenSorts); // [Bool, Int, Float, Char, String, List, Set, Map]
        builder.addAll(TOKEN_SORTS); // e.g., [#String, #Int, Id, #Float]
        builtinSorts = builder.build();
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
        return builtinSorts;
    }

    /**
     * @see Context#getTokenSorts()
     */
    public Set<Sort> tokenSorts() {
        // TODO(YilongL): delegate to context.getTokenSorts() once all String representation of sorts are eliminated
        // return context.getTokenSorts();
        return tokenSorts;
    }

    public Set<Sort> allSorts() {
        return subsorts.allSorts();
    }

    public Subsorts subsorts() {
        return subsorts;
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
}
