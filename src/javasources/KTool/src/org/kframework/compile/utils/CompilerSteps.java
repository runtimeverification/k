// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.AbstractTransformer;
import org.kframework.utils.Stopwatch;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a compound compilation step which consists of a list of
 * compilation steps.
 *
 * @param <T>
 */
public class CompilerSteps<T extends ASTNode> extends BasicCompilerStep<T> {

    List<CompilerStep<T>> steps;

    public CompilerSteps(Context context) {
        super(context);
        steps = new ArrayList<CompilerStep<T>>();
    }

    public CompilerSteps(List<CompilerStep<T>> ts, Context context) {
        super(context);
        this.steps = new ArrayList<CompilerStep<T>>(ts);
    }

    public void add(CompilerStep<T> t) {
        steps.add(t);
    }

    public void add(AbstractTransformer<RuntimeException> t) {
        steps.add(new CompilerTransformerStep<T>(t, context));
    }

    @Override
    public T compile(T def, String stepName) throws CompilerStepDone {
        for (CompilerStep<T> step : steps) {
            step.setSw(sw);
            def = step.compile(def, stepName);
            if (step.getName().equals(stepName)) {
                throw new CompilerStepDone(def);
            }
        }
        return def;
    }

    @Override
    public String getName() {
        String result = "Aggregated transformers:\n";
        for (CompilerStep<T> t : steps) {
            result+= "\t" + t.getName() + "\n";
        }
        return result;
    }

}
