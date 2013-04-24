package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Term;
import org.kframework.kil.Definition;
//import org.kframework.kil.Rule;
//import org.kframework.kil.Term;
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

import java.util.Set;

import edu.uci.ics.jung.graph.DirectedGraph;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/15/13
 * Time: 12:51 PM
 * To change this template use File | Settings | File Templates.
 */
public class JavaSymbolicKRun implements KRun {
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

            SymbolicRewriter symbolicRewriter = new SymbolicRewriter(definition);
            symbolicRewriter.rewrite(Term.of(cfg));
            //symbolicRewriter.rewriteStar(Term.of(cfg));
            //return new KRunResult<KRunState>(new KRunState(symbolicRewriter.rewrite(cfg)));
            return new KRunResult<KRunState>(new KRunState(cfg));
        } catch (FileNotFoundException e) {
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
