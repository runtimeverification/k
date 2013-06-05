package org.kframework.backend.java.symbolic;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.java.builtins.BuiltinFunction;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Term;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.KRun;
import org.kframework.krun.api.KRunDebugger;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.SearchType;
import org.kframework.krun.api.Transition;
import org.kframework.utils.BinaryLoader;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;


/**
 *
 *
 * @author AndreiS
 */
public class JavaSymbolicKRun implements KRun {
	
	private Context context;
	
	public JavaSymbolicKRun(Context context) {
		this.context = context;
	}
	
    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {
        try {
            /* load the definition from a binary file */
            InputStream inputStream = new BufferedInputStream(new FileInputStream(
                    JavaSymbolicBackend.DEFINITION_FILENAME));
            Definition definition = (Definition) BinaryLoader.fromBinary(inputStream);
            inputStream.close();

            /* initialize the builtin function table */
            BuiltinFunction.init(context);

            SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition, context);
            symbolicRewriter.rewrite(Term.of(cfg, context));
            //symbolicRewriter.rewriteStar(Term.of(cfg, context));
            return new KRunResult<KRunState>(new KRunState(cfg, context));
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (MatcherException e) {
            e.printStackTrace();
        }
        return null;
    }

	@Override
	public KRunResult<SearchResults> search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            RuleCompilerSteps compilationInfo) throws KRunExecutionException {
        throw new UnsupportedOperationException();
    }

    @Override
    public KRunResult<DirectedGraph<KRunState, Transition>> modelCheck(
            org.kframework.kil.Term formula,
            org.kframework.kil.Term cfg) throws KRunExecutionException {
        throw new UnsupportedOperationException();
    }

    @Override
    public KRunResult<KRunState> step(org.kframework.kil.Term cfg, int steps)
            throws KRunExecutionException {
        throw new UnsupportedOperationException();
    }

    @Override
    public KRunDebugger debug(org.kframework.kil.Term cfg) {
        throw new UnsupportedOperationException();
    }

    @Override
    public KRunDebugger debug(DirectedGraph<KRunState, Transition> graph) {
        throw new UnsupportedOperationException();
    }

}
