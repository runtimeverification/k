// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Combines a list of {@code LocalTransformer}s.
 *
 * @author Traian
 */
public class CombinedLocalTransformer extends LocalTransformer {

    private final List<LocalTransformer> transformers;

    public CombinedLocalTransformer() {
        transformers = new ArrayList<>();
    }

    public CombinedLocalTransformer(LocalTransformer ... localTransformers) {
        this();
        transformers.addAll(Arrays.asList(localTransformers));
    }

    public void addTransformer(LocalTransformer t) {
        transformers.add(t);
    }

    @Override
    public String getName() {
        String name = "Combined Transformer:\n";
        for (Transformer t : transformers) {
            name += "\t" + t.getName() + "\n";
        }
        return name;
    }

    /**
     * Applies all internal transformers on the given node in order.
     */
    private JavaSymbolicObject transformAll(JavaSymbolicObject node) {
        for (Transformer t : transformers) {
            JavaSymbolicObject astNode = node.accept(t);
            if (!(astNode instanceof JavaSymbolicObject))
                return astNode;
            node = (JavaSymbolicObject) astNode;
        }
        return node;
    }

    @Override
    public JavaSymbolicObject transform(BitVector node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(BoolToken node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(BuiltinList node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(BuiltinMap node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(BuiltinSet node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(Collection node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(ConstrainedTerm node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(Hole node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(IntToken node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KLabelConstant node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KLabelInjection node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KItem node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KCollection node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KLabel node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KList node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(KSequence node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(MetaVariable node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(Rule node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(ConjunctiveFormula node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(DisjunctiveFormula node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(Term node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(Token node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(UninterpretedToken node) {
        return transformAll(node);
    }

    @Override
    public JavaSymbolicObject transform(Variable node) {
        return transformAll(node);
    }
}
