package org.kframework.backend.java.symbolic;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.indexing.TopIndex;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResult;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.api.Transition;
import org.kframework.utils.BinaryLoader;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;


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
            /* initialize the builtin function table */
            BuiltinFunction.init(context);

            /* load the definition from a binary file */
            InputStream inputStream = new BufferedInputStream(new FileInputStream(
                    JavaSymbolicBackend.DEFINITION_FILENAME));
            org.kframework.kil.Definition kilDefinition = (org.kframework.kil.Definition)
                    BinaryLoader.fromBinary(inputStream);
            definition = (Definition) (kilDefinition).accept(transformer);
            inputStream.close();
        } catch (FileNotFoundException e) {
            throw new KRunExecutionException(e);
        } catch (IOException e) {
            throw new KRunExecutionException(e);
        } catch (TransformerException e) {
            throw new KRunExecutionException(e);
        }
	}
	
    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {
        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition, context);
        ConstrainedTerm constrainedTerm = new ConstrainedTerm(Term.of(cfg, context), context);
        ConstrainedTerm result = symbolicRewriter.rewrite(constrainedTerm);

        org.kframework.kil.Term kilTerm = (org.kframework.kil.Term) result.term().accept(
                new BackendJavaKILtoKILTranslation(context));
        return new KRunResult<KRunState>(new KRunState(kilTerm, context));
    }

    @Override
    public KRunProofResult<Set<org.kframework.kil.Term>> prove(org.kframework.kil.Module module) {
        List<Rule> rules = new ArrayList<Rule>();
        for (org.kframework.kil.ModuleItem moduleItem : module.getItems()) {
            assert moduleItem instanceof org.kframework.kil.Rule;

            try {
                rules.add((Rule) moduleItem.accept(transformer));
            } catch (TransformerException e) {
                e.printStackTrace();
            }
        }

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition, context);
        symbolicRewriter.prove(rules);

        throw new UnsupportedOperationException("--prove");
    }

	@Override
	public KRunResult<SearchResults> search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        if (bound != null || depth != null || searchType != SearchType.FINAL) {
            throw new UnsupportedOperationException();
        }

        SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition, context);
        ConstrainedTerm initialTerm = new ConstrainedTerm(Term.of(cfg, context), context);
        ConstrainedTerm targetTerm = new ConstrainedTerm(Term.of(cfg, context), context);
        List<Rule> claims;
        if (pattern != null) {
            claims = Collections.singletonList(new Rule(
                    initialTerm,
                    targetTerm,
                    BoolToken.TRUE,
                    new SymbolicConstraint(context),
                    new IndexingPair(TopIndex.TOP, TopIndex.TOP),
                    new Attributes()));
        } else {
            claims = Collections.emptyList();
        }

        List<SearchResult> searchResults = new ArrayList<SearchResult>();
        for (ConstrainedTerm result : symbolicRewriter.search(initialTerm, targetTerm, claims)) {
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
    public KRunProofResult<DirectedGraph<KRunState, Transition>> modelCheck(
            org.kframework.kil.Term formula,
            org.kframework.kil.Term cfg) throws KRunExecutionException {
        throw new UnsupportedOperationException("--ltlmc");
    }

    @Override
    public KRunResult<KRunState> step(org.kframework.kil.Term cfg, int steps)
            throws KRunExecutionException {
        throw new UnsupportedOperationException("--debug");
    }

    @Override
    public KRunDebugger debug(org.kframework.kil.Term cfg) {
        throw new UnsupportedOperationException("--debug");
    }

    @Override
    public KRunDebugger debug(DirectedGraph<KRunState, Transition> graph) {
        throw new UnsupportedOperationException("--debug");
    }

	@Override
	public void setBackendOption(String key, Object value) {
	}

}
