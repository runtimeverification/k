package org.kframework.backend.unparser;

import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Term;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResult;
import org.kframework.transformation.Transformation;

public class KASTOutputMode {

    private KASTOutputMode() {}

    public static class PrintKRunState implements Transformation<KRunState, ASTNode> {

        @Override
        public Term run(KRunState state, Attributes a) {
            return state.getRawResult();
        }

        @Override
        public String getName() {
            return "--output kast : convert state to term";
        }

    }

    public static class PrintSearchResult implements Transformation<SearchResult, Map<String, Term>> {

        @Override
        public Map<String, Term> run(SearchResult solution, Attributes a) {
            return solution.getRawSubstitution();
        }

        @Override
        public String getName() {
            return "--output kast : convert search result to substitution";
        }

    }
}
