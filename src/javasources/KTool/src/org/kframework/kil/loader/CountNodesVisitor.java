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
    public void visit(Module module) {
        if (!module.isPredefined()) {
            context.numModules++;
            super.visit(module);
        }
    }

    @Override
    public void visit(Sentence rule) {
        context.numSentences++;
        super.visit(rule);
    }

    @Override
    public void visit(Production production) {
        context.numProductions++;
        super.visit(production);
    }

    boolean inConfig = false;
    @Override
    public void visit(Configuration config) {
        inConfig = true;
        super.visit(config);
        inConfig = false;
        context.numSentences++;
    }

    @Override
    public void visit(Cell cell) {
        if (inConfig) {
            context.numCells++;
            super.visit(cell);
        }
    }
}
