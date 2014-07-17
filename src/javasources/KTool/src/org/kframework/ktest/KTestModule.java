// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.ktest;

import org.kframework.ktest.CmdArgs.KTestOptions;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import com.google.inject.AbstractModule;

public class KTestModule extends AbstractModule {

    private final KTestOptions options;

    public KTestModule(KTestOptions options) {
        this.options = options;
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KTestFrontEnd.class);
        bind(KTestOptions.class).toInstance(options);
        bind(GlobalOptions.class).toInstance(options.getGlobal());
    }

}
