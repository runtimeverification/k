// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.utils;

import com.google.inject.Inject;
import org.apache.commons.lang3.NotImplementedException;
import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;

/**
    A dummy backend which just exists as a non-abstract Backend instance
    for tests of injection and argument parsing.

    Methods throw a NotImplementedException, except for those which can
    be called during injection
 */
public class TestBackend implements Backend {
    public TestBackend() {
    }

    @Override
    public void run(Definition definition) {
        throw new NotImplementedException("TestBackend does not actually implement anything");
    }

    @Override
    public String getDefaultStep() {
        throw new NotImplementedException("TestBackend does not actually implement anything");
    }

    @Override
    public Definition firstStep(Definition def) {
        throw new NotImplementedException("TestBackend does not actually implement anything");
    }

    @Override
    public Definition lastStep(Definition def) {
        throw new NotImplementedException("TestBackend does not actually implement anything");
    }

    /**
     * This method is called during injection to get a value for
     * Booleans annotated with {@link org.kframework.backend.Backend.Autoinclude}
     * @return
     */
    @Override
    public boolean autoinclude() {
        return true;
    }

    /**
     * This method is called during injection to get a value for
     * Strings annotated with {@link org.kframework.backend.Backend.AutoincludedFile}
     * @return
     */
    @Override
    public String autoincludedFile() {
        return "TestBackend dummy autoincludedFile() result";
    }

    @Override
    public boolean generatesDefinition() {
        throw new NotImplementedException("TestBackend does not actually implement anything");
    }

    @Override
    public CompilerSteps<Definition> getCompilationSteps() {
        throw new NotImplementedException("TestBackend does not actually implement anything");
    }
}
