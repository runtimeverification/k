package org.kframework.backend.unparser;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;

public class NoOutputMode implements Transformation<KRunResult<?>, String> {

    @Override
    public String run(KRunResult<?> result, Attributes a) {
        return "";
    }

    @Override
    public String getName() {
        return "no output";
    }
}
