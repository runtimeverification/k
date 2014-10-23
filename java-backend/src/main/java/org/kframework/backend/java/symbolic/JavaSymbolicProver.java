// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.compile.DataStructureToLookupUpdate;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.compile.transformers.DataStructure2Cell;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.ConfigurationSubstitutionVisitor;
import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.Module;
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
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(Module module, org.kframework.kil.Term cfg) throws KRunExecutionException {
        TermContext termContext = TermContext.of(globalContext);
        Map<org.kframework.kil.Term, org.kframework.kil.Term> substitution = null;
        if (cfg != null) {
            cfg = executor.run(cfg).getResult().getRawResult();
            cfg = (org.kframework.kil.Term) (new DataStructure2Cell(context)).visitNode(cfg);
            ConfigurationSubstitutionVisitor configurationSubstitutionVisitor =
                    new ConfigurationSubstitutionVisitor(context);
            configurationSubstitutionVisitor.visitNode(cfg);
            substitution = configurationSubstitutionVisitor.getSubstitution();
//            System.out.println(substitution);
            Module mod = module;
            mod = (Module) new Substitution(substitution,context).visitNode(module);
//                System.out.println(mod.toString());
            module = mod;
        }
        try {
            module = new SpecificationCompilerSteps(context, kem).compile(module, null);
        } catch (CompilerStepDone e) {
            assert false: "dead code";
        }
        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();

        DataStructureToLookupUpdate mapTransformer = new DataStructureToLookupUpdate(context);

        List<Rule> rules = new ArrayList<Rule>();
        for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
            if (!(moduleItem instanceof org.kframework.kil.Rule)) {
                continue;
            }

            Rule rule = transformer.transformAndEval(
                    (org.kframework.kil.Rule) mapTransformer.visitNode(moduleItem));
            Rule freshRule = rule.getFreshRule(termContext);
            rules.add(freshRule);
        }

        SymbolicRewriter symbolicRewriter = executor.getSymbolicRewriter();
        for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
            if (!(moduleItem instanceof org.kframework.kil.Rule)) {
                continue;
            }

            org.kframework.kil.Rule kilRule = (org.kframework.kil.Rule) moduleItem;
            org.kframework.kil.Term kilLeftHandSide
                    = ((org.kframework.kil.Rewrite) kilRule.getBody()).getLeft();
            org.kframework.kil.Term kilRightHandSide =
                    ((org.kframework.kil.Rewrite) kilRule.getBody()).getRight();
            org.kframework.kil.Term kilRequires = kilRule.getRequires();
            org.kframework.kil.Term kilEnsures = kilRule.getEnsures();

            org.kframework.kil.Rule kilDummyRule = new org.kframework.kil.Rule(
                    kilRightHandSide,
                    MetaK.kWrap(org.kframework.kil.KSequence.EMPTY, "k"),
                    kilRequires,
                    kilEnsures,
                    context);
            Rule dummyRule = transformer.transformAndEval(
                    (org.kframework.kil.Rule) mapTransformer.visitNode(kilDummyRule));

            SymbolicConstraint initialConstraint = new SymbolicConstraint(termContext);
            initialConstraint.addAll(dummyRule.requires());
            ConstrainedTerm initialTerm = new ConstrainedTerm(
                    transformer.transformAndEval(kilLeftHandSide),
                    initialConstraint);

            SymbolicConstraint targetConstraint = new SymbolicConstraint(termContext);
            targetConstraint.addAll(dummyRule.ensures());
            ConstrainedTerm targetTerm = new ConstrainedTerm(
                    dummyRule.leftHandSide().evaluate(termContext),
                    dummyRule.lookups().getSymbolicConstraint(termContext),
                    targetConstraint);

            proofResults.addAll(symbolicRewriter.proveRule(initialTerm, targetTerm, rules));
        }

        System.err.println(proofResults.isEmpty());
        System.err.println(proofResults);

        return new KRunProofResult<Set<org.kframework.kil.Term>>(
                proofResults.isEmpty(), Collections.<org.kframework.kil.Term>emptySet());
    }
}
