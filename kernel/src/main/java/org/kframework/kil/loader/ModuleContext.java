// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.kframework.kil.Attribute;
import org.kframework.kil.Cell;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.utils.Poset;

import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

public class ModuleContext implements Serializable {
    /** set of imported modules into this module. Should contain the auto included ones */
    private Set<Module> importedModules = new HashSet<>();
    /** declared sorts visible in this module (transitive) */
    private Set<Sort> declaredSorts = new HashSet<>();
    /** syntactic subsorts visible in this module (transitive) */
    private Poset<Sort> syntacticSubsorts = Poset.create();
    /** multimap from a klabel to a production visible in this m/odule (transitive) */
    public SetMultimap<String, Production> klabels = HashMultimap.create();
    /** multimap from a tag to a production visible in this module (transitive) */
    public SetMultimap<String, Production> tags = HashMultimap.create();
    public Map<String, Cell> cells = new HashMap<>();
    public Map<String, Sort> cellSorts = new HashMap<>();
    private Poset<String> priorities = Poset.create();
    private Poset<String> assocLeft = Poset.create();
    private Poset<String> assocRight = Poset.create();

    private Grammar ruleGrammar = null;

    /**
     * Represents the bijection map between conses and productions.
     */
    public Set<Production> productions = new HashSet<>();
    public Map<Sort, Production> listProductions = new LinkedHashMap<>();
    public SetMultimap<String, Production> listKLabels = HashMultimap.create();

    public void add(ModuleContext moduleContext) {
        this.importedModules.addAll(moduleContext.importedModules);
        this.declaredSorts.addAll(moduleContext.declaredSorts);
        this.syntacticSubsorts.add(moduleContext.syntacticSubsorts);
        this.klabels.putAll(moduleContext.klabels);
        this.tags.putAll(moduleContext.tags);
        this.cells.putAll(moduleContext.cells);
        this.cellSorts.putAll(moduleContext.cellSorts);
        this.priorities.add(moduleContext.priorities);
        this.assocLeft.add(moduleContext.assocLeft);
        this.assocRight.add(moduleContext.assocRight);
    }

    public void addProduction(Production p) {
        productions.add(p);
        if (p.getKLabel() != null) {
            klabels.put(p.getKLabel(), p);
            tags.put(p.getKLabel(), p);
            if (p.isListDecl()) {
                listKLabels.put(p.getTerminatorKLabel(), p);
            }
        }
        if (p.isListDecl()) {
            listProductions.put(p.getSort(), p);
        }
        for (Attribute<?> a : p.getAttributes().values()) {
            tags.put(a.getKey().toString(), p);
        }
    }

    public void removeProduction(Production p) {
        productions.remove(p);
        if (p.getKLabel() != null) {
            klabels.remove(p.getKLabel(), p);
            tags.remove(p.getKLabel(), p);
            if (p.isListDecl()) {
                listKLabels.remove(p.getTerminatorKLabel(), p);
            }
        }
        if (p.isListDecl()) {
            // AndreiS: this code assumes each list sort has only one production
            listProductions.remove(p.getSort());
        }
        for (Attribute<?> a : p.getAttributes().values()) {
            tags.remove(a.getKey().toString(), p);
        }
    }

    public void addImportedModule(Module mod) {
        importedModules.add(mod);
    }

    public Set<Module> getImportedModules() {
        return java.util.Collections.unmodifiableSet(importedModules);
    }

    public void addDeclaredSort(Sort sort) {
        declaredSorts.add(sort);
    }

    public Set<Sort> getDeclaredSorts() {
        return java.util.Collections.unmodifiableSet(declaredSorts);
    }

    public void addSyntacticSubsort(Sort bigSort, Sort smallSort) {
        syntacticSubsorts.addRelation(bigSort, smallSort);
    }

    public Grammar getRuleGrammar() {
        return ruleGrammar;
    }

    public void setRuleGrammar(Grammar ruleGrammar) {
        this.ruleGrammar = ruleGrammar;
    }
}
