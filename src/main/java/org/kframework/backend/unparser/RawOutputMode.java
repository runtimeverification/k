package org.kframework.backend.unparser;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;

public class RawOutputMode {

    private RawOutputMode() {}

    public static class PrintKRunResult implements Transformation<KRunResult<?>, String> {

        @Override
        public String run(KRunResult<?> result, Attributes a) {
            return result.getRawOutput();
        }

        @Override
        public String getName() {
            return "--output raw : print result of execution";
        }

    }

    public static class PrintASTNode implements Transformation<ASTNode, String> {

        @Override
        public String run(ASTNode t, Attributes a) {
            return t.toString();
        }

        @Override
        public String getName() {
            return "--output raw : print term";
        }

    }
}
