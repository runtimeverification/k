// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.loader.Context;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Sentence;

import org.kframework.kil.visitors.BasicVisitor;

public class CountNodesVisitor extends BasicVisitor {
    public CountNodesVisitor(Context context) {
        super(context);
        context.numModules = 0;
        context.numSentences = 0;
        context.numProductions = 0;
        context.numCells = 0;
    }

    @Override
    public Void visit(Module module, Void _) {
        if (!module.isPredefined()) {
            context.numModules++;
            super.visit(module, _);
        }
        return null;
    }

    @Override
    public Void visit(Sentence rule, Void _) {
        context.numSentences++;
        return super.visit(rule, _);
    }

    @Override
    public Void visit(Production production, Void _) {
        context.numProductions++;
        return super.visit(production, _);
    }

    boolean inConfig = false;
    @Override
    public Void visit(Configuration config, Void _) {
        inConfig = true;
        super.visit(config, _);
        inConfig = false;
        context.numSentences++;
        return null;
    }

    @Override
    public Void visit(Cell cell, Void _) {
        if (inConfig) {
            context.numCells++;
            super.visit(cell, _);
        }
        return null;
    }
}
