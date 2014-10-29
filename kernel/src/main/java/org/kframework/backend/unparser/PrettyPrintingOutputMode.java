// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResult;
import org.kframework.transformation.Transformation;

import com.google.inject.Inject;

public class PrettyPrintingOutputMode  {

    private PrettyPrintingOutputMode() {}

    public static class PrintKRunState implements Transformation<KRunState, ASTNode> {

        private final ConcretizeTerm concretizer;

        @Inject
        public PrintKRunState(ConcretizeTerm concretizer) {
            this.concretizer = concretizer;
        }

        @Override
        public Term run(KRunState state, Attributes a) {
            return concretizer.concretize(a.typeSafeGet(Context.class), state.getRawResult());
        }

        @Override
        public String getName() {
            return "--output pretty : convert state to term";
        }
    }

    public static class PrintSearchResult implements Transformation<SearchResult, Map<String, Term>> {

        private final ConcretizeTerm concretizer;

        @Inject
        public PrintSearchResult(ConcretizeTerm concretizer) {
            this.concretizer = concretizer;
        }

        @Override
        public Map<String, Term> run(SearchResult solution, Attributes a) {
            return concretizer.concretizeSubstitution(a.typeSafeGet(Context.class), solution);
        }

        @Override
        public String getName() {
            return "--output pretty : convert search result to substitution";
        }

    }
}
