// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.Attributes;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.transformation.Transformation;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

/**
 * Created by dwightguth on 4/30/15.
 */
public class KRun implements Transformation<Void, Void> {

    private final KExceptionManager kem;
    private final FileUtil files;

    public KRun(KExceptionManager kem, FileUtil files) {
        this.kem = kem;
        this.files = files;
    }

    public int run(CompiledDefinition compiledDef, KRunOptions options) {
        System.err.println("TODO(cos): krun");
        return 0;
    }

    @Override
    public Void run(Void aVoid, Attributes attrs) {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }
}
