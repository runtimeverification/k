// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.kframework.kil.Attribute;
import org.kframework.kil.Cell;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.utils.Poset;

import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

public class ModuleContext implements Serializable {
    private Set<Module> importedModules;
    private Set<Sort> declaredSorts;
    private Poset<Sort> syntacticSubsorts = Poset.create();
    public SetMultimap<String, Production> klabels = HashMultimap.create();
    public SetMultimap<String, Production> tags = HashMultimap.create();
    public Map<String, Cell> cells = new HashMap<>();
    public Map<String, Sort> cellSorts = new HashMap<>();
    private Poset<String> priorities = Poset.create();
    private Poset<String> assocLeft = Poset.create();
    private Poset<String> assocRight = Poset.create();

    /**
     * Represents the bijection map between conses and productions.
     */
    public Set<Production> productions = new HashSet<>();
    public Map<Sort, Production> listProductions = new LinkedHashMap<>();
    public SetMultimap<String, Production> listKLabels = HashMultimap.create();

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
}
