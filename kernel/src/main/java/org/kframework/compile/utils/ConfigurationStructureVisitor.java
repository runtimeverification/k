// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import com.google.common.collect.Sets;

import java.util.Stack;

/**
 * Visitor populating the configurationStructureMap of a given Context object.
 * @see ConfigurationStructureMap for additional info about this structure.
 */
public class ConfigurationStructureVisitor extends BasicVisitor {

    Stack<ConfigurationStructure> ancestors = new Stack<ConfigurationStructure>();

    private ConfigurationStructureMap config;
    private int maxLevel = 0;

    public ConfigurationStructureVisitor(Context context) {
        super(context);
        this.config = context.getConfigurationStructureMap();
        this.config.clear();
    }

    @Override
    public Void visit(Configuration node, Void _void) {
        Term t = node.getBody();
        Cell top = new Cell();
        top.setLabel(MetaK.Constants.generatedCfgAbsTopCellLabel);
        top.setId(MetaK.Constants.generatedCfgAbsTopCellLabel);
        top.setContents(t);
        this.visitNode(top);
        return null;
    }

    @Override
    public Void visit(Cell node, Void _void) {
        ConfigurationStructure cfg = new ConfigurationStructure();
        cfg.multiplicity = node.getMultiplicity();
        cfg.id = node.getId();
        cfg.cell = node;
        cfg.ancestorIds = Sets.newHashSet();
        if (!ancestors.empty()) {
            ConfigurationStructure parent = ancestors.peek();
            cfg.level = parent.level+1;
            cfg.parent = parent;
            if (cfg.level > maxLevel) maxLevel = cfg.level;
            parent.sons.put(cfg.id, cfg);
            for (ConfigurationStructure cfgStruct : ancestors) {
                cfg.ancestorIds.add(cfgStruct.id);
            }
        }
        ancestors.push(cfg);
        super.visit(node, _void);
        ancestors.pop();
        config.put(cfg.id, cfg);
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Syntax node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Rule node, Void _void) {
        return null;
    }

    public int getMaxLevel() {
        return maxLevel;
    }
}
