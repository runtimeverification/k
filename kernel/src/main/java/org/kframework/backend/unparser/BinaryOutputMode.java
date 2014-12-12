// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.io.ByteArrayOutputStream;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.transformation.Transformation;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;

import com.google.inject.Inject;
import com.sun.org.apache.xerces.internal.impl.dv.util.Base64;

public class BinaryOutputMode implements Transformation<KRunResult, String> {

    private final BinaryLoader loader;

    @Inject
    BinaryOutputMode(
            BinaryLoader loader,
            KExceptionManager kem) {
        this.loader = loader;
    }

    @Override
    public String run(KRunResult result, Attributes a) {
        ByteArrayOutputStream os = new ByteArrayOutputStream();

        Object toSerialize = result;
        if (result instanceof KRunState) {
            toSerialize = ((KRunState)result).getRawResult();
        } else if (result instanceof SearchResults) {
            toSerialize = ((SearchResults)result).getGraph();
        }

        loader.saveOrDie(os, toSerialize);
        return Base64.encode(os.toByteArray());
    }

    @Override
    public String getName() {
        return "--output binary";
    }

}
