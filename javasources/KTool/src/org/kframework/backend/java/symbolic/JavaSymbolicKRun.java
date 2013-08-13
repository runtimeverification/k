package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.indexing.TopIndex;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.MapToLookupUpdate;
import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.RuleCompilerSteps;
//import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.*;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.utils.BinaryLoader;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.Collection;
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
		this.context = context;
        transformer = new KILtoBackendJavaKILTransformer(context);

        try {
            /* load the definition from a binary file */
            InputStream inputStream = new BufferedInputStream(new FileInputStream(new File(
                    context.kompiled,
                    JavaSymbolicBackend.DEFINITION_FILENAME)));
            org.kframework.kil.Definition kilDefinition
                    = (org.kframework.kil.Definition) BinaryLoader.fromBinary(inputStream);
            definition = transformer.transformDefinition(kilDefinition);
            inputStream.close();

            if (definition == null) {
                throw new KRunExecutionException("cannot load definition");
            }

            /* initialize the builtin function table */
            BuiltinFunction.init(definition);
        } catch (FileNotFoundException e) {
            throw new KRunExecutionException(e);
        } catch (IOException e) {
            throw new KRunExecutionException(e);
        }
	}
	
    public static Cell wrap(Term t, String label) {
        Cell cell = new Cell(label,t);
        System.out.println("Content Kind: "+t.kind());
        return cell;
    }

    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(Term.of(cfg, definition), new TermContext(definition, new PortableFileSystem()));
        ConstrainedTerm result = symbolicRewriter.rewrite(constrainedTerm);
        org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                new BackendJavaKILtoKILTranslation(context));
        return new KRunResult<KRunState>(new KRunState(kilTerm, context));
    }

    @Override
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(org.kframework.kil.Module module) {
        List<ConstrainedTerm> proofResults = new ArrayList<ConstrainedTerm>();

        MapToLookupUpdate mapTransformer = new MapToLookupUpdate(context);

        try {
            List<Rule> rules = new ArrayList<Rule>();
            for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
                assert moduleItem instanceof org.kframework.kil.Rule;

                rules.add(transformer.transformRule(
                        (org.kframework.kil.Rule) moduleItem.accept(mapTransformer),
                        definition));
            }

            SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
            for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
                org.kframework.kil.Rule kilRule = (org.kframework.kil.Rule) moduleItem;
                org.kframework.kil.Term kilLeftHandSide
                        = ((org.kframework.kil.Rewrite) kilRule.getBody()).getLeft();
                org.kframework.kil.Term kilRightHandSide =
                        ((org.kframework.kil.Rewrite) kilRule.getBody()).getRight();
                org.kframework.kil.Term kilRequires = kilRule.getRequires();

                //TODO: Deal with Ensures
                
                /* rename rule variables */
                Map<Variable, Variable> freshSubstitution = Variable.getFreshSubstitution(
                        transformer.transformRule(
                                (org.kframework.kil.Rule) moduleItem.accept(mapTransformer),
                                definition).variableSet());

                TermContext termContext = new TermContext(definition, new PortableFileSystem());
                SymbolicConstraint initialConstraint = new SymbolicConstraint(termContext);
                //initialConstraint.addAll(rule.condition());
                initialConstraint.add(
                        transformer.transformTerm(kilRequires, definition),
                        BoolToken.TRUE);
                ConstrainedTerm initialTerm = new ConstrainedTerm(
                        transformer.transformTerm(kilLeftHandSide, definition).substitute(
                                freshSubstitution,
                                termContext),
                        initialConstraint.substitute(freshSubstitution, termContext),
                        termContext);

                org.kframework.kil.Rule kilDummyRule = new org.kframework.kil.Rule(
                        kilRightHandSide,
                        MetaK.kWrap(org.kframework.kil.KSequence.EMPTY, "k"),
                        context);
                Rule dummyRule = transformer.transformRule(
                        (org.kframework.kil.Rule) kilDummyRule.accept(mapTransformer),
                        definition);
                ConstrainedTerm targetTerm = new ConstrainedTerm(
                        dummyRule.leftHandSide().substitute(freshSubstitution, termContext),
                        dummyRule.lookups().substitute(freshSubstitution, termContext),
                        new SymbolicConstraint(termContext),
                        termContext);

                proofResults.addAll(symbolicRewriter.proveRule(initialTerm, targetTerm, rules));
            }

            return null;
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

    public KRunResult<GeneratorResults> generate(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        //for now, test generation uses the "search-all" option
        //we hope to add strategies on top of this in the future
        if (searchType != SearchType.STAR) {
            throw new UnsupportedOperationException("Search type should be SearchType.STAR");
        }

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
        TermContext termContext = new TermContext(definition, new PortableFileSystem());
        ConstrainedTerm initialTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);
        ConstrainedTerm targetTerm = new ConstrainedTerm(Term.of(cfg, definition), termContext);


        List<Rule> claims = Collections.emptyList();
        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        List<GeneratorResult> generatedPrograms = new ArrayList<GeneratorResult>();

        List<ConstrainedTerm> hits = symbolicRewriter.search(initialTerm, targetTerm, claims, bound, depth, true);

        for (ConstrainedTerm result : hits ) {
            //reconstruct the generated program
            Term pgm = constructProgram(result,Term.of(cfg,definition));

            org.kframework.kil.Term pgmTerm =  (org.kframework.kil.Term)  pgm.accept(
                    new BackendJavaKILtoKILTranslation(context));

            org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                    new BackendJavaKILtoKILTranslation(context));

            generatedPrograms.add(new GeneratorResult(
                    new KRunState(kilTerm, context),
                    Collections.singletonMap("B:Bag", kilTerm),
                    compilationInfo,
                    context,
                    pgmTerm));
        }

        return new KRunResult<GeneratorResults>(new GeneratorResults(
                generatedPrograms,
                null,
                true,
                context));
    }

    private Term constructProgram(ConstrainedTerm term, Term config){
        SymbolicConstraint constraint = term.constraint();
        Term pgm = config.substitute(constraint.substitution(),term.termContext());
        return pgm;
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
        throw new UnsupportedBackendOptionException("--debug");
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
