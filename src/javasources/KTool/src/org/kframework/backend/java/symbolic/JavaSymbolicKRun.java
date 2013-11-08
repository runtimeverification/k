package org.kframework.backend.java.symbolic;


import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.compile.transformers.DataStructureToLookupUpdate;
import org.kframework.compile.utils.*;
//import org.kframework.kil.*;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.*;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.utils.BinaryLoader;

import java.io.File;
import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Set;


import edu.uci.ics.jung.graph.DirectedGraph;


/**
 *
 *
 * @author AndreiS
 */
public class JavaSymbolicKRun implements KRun {

    private final Definition definition;
	private final Context context;
    private final KILtoBackendJavaKILTransformer transformer;

    public JavaSymbolicKRun(Context context) throws KRunExecutionException {
        /* context is unused for directory paths; the actual context is de-serialized */
        /* load the definition from a binary file */
        definition = (Definition) BinaryLoader.load(
            new File(context.kompiled, JavaSymbolicBackend.DEFINITION_FILENAME).toString());

        if (definition == null) {
            throw new KRunExecutionException("cannot load definition");
        }

        /* initialize the builtin function table */
        BuiltinFunction.init(definition);

        this.context = definition.context();
        this.context.kompiled = context.kompiled;
        transformer = new KILtoBackendJavaKILTransformer(this.context);
	}

    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {
        return internalRun(cfg, -1);
    }

    private KRunResult<KRunState> internalRun(org.kframework.kil.Term cfg, int bound) throws KRunExecutionException {
        ConstrainedTerm result = javaKILRun(cfg, bound);
        org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                new BackendJavaKILtoKILTranslation(context));
        return new KRunResult<KRunState>(new KRunState(kilTerm, context));
    }

    private ConstrainedTerm javaKILRun(org.kframework.kil.Term cfg, int bound) {
        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        Term term = Term.of(cfg, definition);
        TermContext termContext = new TermContext(definition, new PortableFileSystem());
        term = term.evaluate(termContext);
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(term, termContext);
        return symbolicRewriter.rewrite(constrainedTerm, bound);
    }

    @Override
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(Module module, org.kframework.kil.Term cfg) throws KRunExecutionException {
        TermContext termContext = new TermContext(definition, new PortableFileSystem());
        Map<org.kframework.kil.Term, org.kframework.kil.Term> substitution = null;
        if (cfg != null) {
            cfg = run(cfg).getResult().getRawResult();
            ConfigurationSubstitutionVisitor configurationSubstitutionVisitor =
                    new ConfigurationSubstitutionVisitor(context);
            cfg.accept(configurationSubstitutionVisitor);
            substitution = configurationSubstitutionVisitor.getSubstitution();
//            System.out.println(substitution);
            Module mod = module;
            try {
                mod = (Module) module.accept(new Substitution(substitution,context));
//                System.out.println(mod.toString());
            } catch (TransformerException e) {
                assert false : "This should not have happened!";
            }
            module = mod;
        }
        try {
            module = new SpecificationCompilerSteps(context).compile(module, null);
        } catch (CompilerStepDone e) {
            assert false: "dead code";
        }
        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();

        DataStructureToLookupUpdate mapTransformer = new DataStructureToLookupUpdate(context);

        try {
            List<Rule> rules = new ArrayList<Rule>();
            for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
                assert moduleItem instanceof org.kframework.kil.Rule;

                Rule rule = transformer.transformRule(
                        (org.kframework.kil.Rule) moduleItem.accept(mapTransformer),
                        definition);
                Rule freshRule = rule.getFreshRule(termContext);
//                System.out.println(freshRule.toString());
            }

            SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
            for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
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
                Rule dummyRule = transformer.transformRule(
                        (org.kframework.kil.Rule) kilDummyRule.accept(mapTransformer),
                        definition);

                SymbolicConstraint initialConstraint = new SymbolicConstraint(termContext);
                //initialConstraint.addAll(rule.condition());
                initialConstraint.addAll(dummyRule.requires());
                ConstrainedTerm initialTerm = new ConstrainedTerm(
                        transformer.transformTerm(kilLeftHandSide, definition),
                        initialConstraint,
                        termContext);

                SymbolicConstraint targetConstraint = new SymbolicConstraint(termContext);
                targetConstraint.addAll(dummyRule.ensures());
                ConstrainedTerm targetTerm = new ConstrainedTerm(
                        dummyRule.leftHandSide(),
                        dummyRule.lookups().getSymbolicConstraint(termContext),
                        targetConstraint,
                        termContext);

//                System.out.println("Initial: " + initialTerm);
//                System.out.println("Target: " + targetTerm);
                proofResults.addAll(symbolicRewriter.proveRule(initialTerm, targetTerm, rules));
            }

            System.err.println(proofResults.isEmpty());
            System.err.println(proofResults);

            return new KRunProofResult<Set<org.kframework.kil.Term>>(
                    proofResults.isEmpty(), Collections.<org.kframework.kil.Term>emptySet());
        } catch (TransformerException e) {
            e.printStackTrace();
            return null;
        }
    }

	@Override
	public KRunResult<SearchResults> search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        FileSystem fs = new PortableFileSystem();
        TermContext termContext = new TermContext(definition, fs);
        ConstrainedTerm initialTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);
        ConstrainedTerm targetTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);
        List<Rule> claims = Collections.emptyList();
        if (bound == null) {
            bound = -1;
        }
        if (depth == null) {
            depth = -1;
        }

        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        List<ConstrainedTerm> hits = symbolicRewriter.search(initialTerm, targetTerm, claims, bound, depth);


        for (ConstrainedTerm result :hits ) {

            org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                    new BackendJavaKILtoKILTranslation(context));

            searchResults.add(new SearchResult(
                    new KRunState(kilTerm, context),
                    Collections.singletonMap("B:Bag", kilTerm),
                    compilationInfo,
                    context));
        }

        return new KRunResult<SearchResults>(new SearchResults(
                searchResults,
                null,
                true,
                context));
    }

	@Override
    public KRunResult<TestGenResults> generate(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        // for now, test generation uses the "search-all" option
        // we hope to add strategies on top of this in the future
        if (searchType != SearchType.STAR) {
            throw new UnsupportedOperationException("Search type should be SearchType.STAR");
        }
        
        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        TermContext termContext = new TermContext(definition, new PortableFileSystem());
        ConstrainedTerm initCfg = new ConstrainedTerm(Term.of(cfg, definition), termContext);

        List<TestGenResult> generatorResults = new ArrayList<TestGenResult>();

//        for (Rule rule : definition.rules()) {
//        	System.out.println(rule);
//        }
        
        if (bound == null) {
            bound = -1;
        }
        if (depth == null) {
            depth = -1;
        }

        List<ConstrainedTerm> resultCfgs = symbolicRewriter.generate(initCfg, null, null, bound, depth);

        for (ConstrainedTerm result : resultCfgs) {
            // construct the generated program by applying the substitution
            // obtained from the result configuration to the initial one
            Term pgm = Term.of(cfg, definition);
            pgm = pgm.substitute(result.constraint().substitution(), termContext);

            org.kframework.kil.Term pgmTerm = (org.kframework.kil.Term) pgm.accept(
                    new BackendJavaKILtoKILTranslation(context));

            org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                    new BackendJavaKILtoKILTranslation(context));

            generatorResults.add(new TestGenResult(
                    new KRunState(kilTerm, context),
                    Collections.singletonMap("B:Bag", kilTerm),
                    compilationInfo,
                    context,
                    pgmTerm,
                    result.constraint()));
        }

        return new KRunResult<TestGenResults>(new TestGenResults(
                generatorResults,
                null,
                true,
                context));
    }

    @Override
    public KRunProofResult<DirectedGraph<KRunState, Transition>> modelCheck(
            org.kframework.kil.Term formula,
            org.kframework.kil.Term cfg) throws KRunExecutionException {
        throw new UnsupportedBackendOptionException("--ltlmc");
    }

    @Override
    public KRunResult<KRunState> step(org.kframework.kil.Term cfg, int steps)
            throws KRunExecutionException {
        return internalRun(cfg, steps);
    }

    @Override
    public KRunDebugger debug(org.kframework.kil.Term cfg) {
        throw new UnsupportedBackendOptionException("--debug");
    }

    @Override
    public KRunDebugger debug(DirectedGraph<KRunState, Transition> graph) {
        throw new UnsupportedBackendOptionException("--debug");
    }

    @Override
    public void setBackendOption(String key, Object value) {
    }

}
