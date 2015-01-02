// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.io.ByteArrayInputStream;
import java.io.InputStream;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunResult;
import org.kframework.transformation.Transformation;

public class NoOutputMode implements Transformation<KRunResult, InputStream> {

    @Override
    public InputStream run(KRunResult result, Attributes a) {
        return new ByteArrayInputStream(new byte[0]);
    }

    @Override
    public String getName() {
        return "no output";
    }
}
