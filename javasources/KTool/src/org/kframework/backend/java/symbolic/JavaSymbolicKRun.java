package org.kframework.backend.java.symbolic;

import edu.uci.ics.jung.graph.DirectedGraph;
import org.kframework.backend.java.kil.Term;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.api.*;
import org.kframework.utils.BinaryLoader;

import java.io.*;
import java.util.Set;

//import org.kframework.kil.Rule;
//import org.kframework.kil.Term;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/15/13
 * Time: 12:51 PM
 * To change this template use File | Settings | File Templates.
 */
public class JavaSymbolicKRun implements KRun {
	
	protected Context context;
	
	public JavaSymbolicKRun(Context context) {
		this.context = context;
	}
	
    @Override
    public KRunResult<KRunState> run(org.kframework.kil.Term cfg) throws KRunExecutionException {
        try {
            InputStream inputStream = new BufferedInputStream(
                    new FileInputStream(JavaSymbolicBackend.DEFINITION_FILENAME));
            Definition definition = (Definition) BinaryLoader.fromBinary(inputStream);
            try {
                inputStream.close();
            } catch (IOException e) {
                e.printStackTrace();
            }

            SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition, context);
            symbolicRewriter.rewrite(Term.of(cfg, context));
            //symbolicRewriter.rewriteStar(Term.of(cfg));
            //return new KRunResult<KRunState>(new KRunState(symbolicRewriter.rewrite(cfg)));
            return new KRunResult<KRunState>(new KRunState(cfg, context));
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (MatcherException e) {
            e.printStackTrace();
        }

        return null;
    }

	@Override
	public KRunResult<SearchResults> search(Integer bound, Integer depth,
											SearchType searchType,
											org.kframework.kil.Rule pattern,
											org.kframework.kil.Term cfg,
											RuleCompilerSteps compilationInfo) throws KRunExecutionException {
		return null;  //To change body of implemented methods use File | Settings | File Templates.
	}

	//	@Override
    public KRunResult<SearchResults> search(
            Integer bound,
            Integer depth,
            SearchType searchType,
            org.kframework.kil.Rule pattern,
            org.kframework.kil.Term cfg,
            Set<String> varNames) throws KRunExecutionException {
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
    public KRunDebugger debug(SearchResults searchResults) {
        throw new UnsupportedOperationException();
    }

}
