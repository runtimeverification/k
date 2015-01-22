// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.io.InputStream;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;

import org.apache.commons.codec.binary.Base64OutputStream;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.kil.Attributes;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResults;
import org.kframework.transformation.Transformation;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

public class BinaryOutputMode implements Transformation<KRunResult, InputStream> {

    private final BinaryLoader loader;

    @Inject
    BinaryOutputMode(
            BinaryLoader loader,
            KExceptionManager kem) {
        this.loader = loader;
    }

    @Override
    public InputStream run(KRunResult result, Attributes a) {

        Object toSerialize = result;
        if (result instanceof KRunState) {
            toSerialize = ((KRunState)result).getRawResult();
        } else if (result instanceof SearchResults) {
            toSerialize = ((SearchResults)result).getGraph();
        }

        final Object o = toSerialize;

        Pair<PipedInputStream, PipedOutputStream> pipe = FileUtil.pipeOutputToInput();
        new Thread(() ->
        {
            loader.saveOrDie(new Base64OutputStream(pipe.getRight()), o);
        }).start();
        return pipe.getLeft();
    }

    @Override
    public String getName() {
        return "--output binary";
    }

}
