// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.compile.transformers.DataStructure2Cell;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.ConfigurationSubstitutionVisitor;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.Attribute;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.tools.Prover;
import org.kframework.utils.errorsystem.KExceptionManager;

import com.google.inject.Inject;

public class JavaSymbolicProver implements Prover {

    private final JavaSymbolicExecutor executor;
    private final GlobalContext globalContext;
    private final KILtoBackendJavaKILTransformer transformer;
    private final KExceptionManager kem;

    private final Context context;

    @Inject
    JavaSymbolicProver(
            Context context,
            GlobalContext globalContext,
            JavaSymbolicExecutor executor,
            KILtoBackendJavaKILTransformer transformer,
            KExceptionManager kem) {
        this.context = context;
        this.executor = executor;
        this.globalContext = globalContext;
        this.transformer = transformer;
        this.kem = kem;
    }

    @Override
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(org.kframework.kil.Module module)
            throws KRunExecutionException {
        List<Rule> rules = module.getItems().stream()
                .filter(r -> r instanceof org.kframework.kil.Rule)
                .map(r -> (org.kframework.kil.Rule) r)
                .map(transformer::transformAndEval)
                .collect(Collectors.toList());

//        CounterGetter counterGetter = new CounterGetter(context);
//                counterGetter.visitNode(module);
//                BigInteger counter = counterGetter.counter.add(BigInteger.ONE);


        SymbolicRewriter symbolicRewriter = executor.getSymbolicRewriter();
        TermContext termContext = TermContext.builder(globalContext).freshCounter(0).build();
        List<ConstrainedTerm> proofResults = rules.stream()
                .filter(r -> !r.containsAttribute(Attribute.TRUSTED_KEY))
                .map(Rule::getFreshRule)
                .map(r -> symbolicRewriter.proveRule(r.createLhsPattern(termContext), r.createRhsPattern(), rules))
                .flatMap(List::stream)
                .collect(Collectors.toList());

        return new KRunProofResult<>(proofResults.isEmpty(), Collections.emptySet());
    }

    @Override
    public org.kframework.kil.Module preprocess(org.kframework.kil.Module module,
                                                org.kframework.kil.Term cfg)
            throws KRunExecutionException {
        if (cfg != null) {
            cfg = executor.run(cfg, false).getFinalState().getRawResult();
            cfg = (org.kframework.kil.Term) (new DataStructure2Cell(context)).visitNode(cfg);
            module = (org.kframework.kil.Module) new Substitution(
                    ConfigurationSubstitutionVisitor.getSubstitution(cfg, context), context).visitNode(module);
        }
        try {
            module = new SpecificationCompilerSteps(context, kem).compile(module, null);
        } catch (CompilerStepDone e) {
            assert false: "dead code";
        }
        return module;
    }

    @SuppressWarnings("unused")
    private static class CounterGetter extends org.kframework.kil.visitors.BasicVisitor {

        public BigInteger counter = BigInteger.ZERO;

        public CounterGetter(Context context) {
            super(context);
        }

        @Override
        public Void visit(IntBuiltin intBuiltin, Void _void) {
            counter = counter.max(intBuiltin.bigIntegerValue());
            return null;
        }

    }

}
