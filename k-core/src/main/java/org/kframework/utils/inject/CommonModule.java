// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import org.kframework.main.Tool;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.general.GlobalSettings;
import com.google.inject.AbstractModule;

public class CommonModule extends AbstractModule {

    @Override
    protected void configure() {
        requestStaticInjection(Stopwatch.class);
        requestStaticInjection(GlobalSettings.class);
        requestStaticInjection(BinaryLoader.class);
        requestStaticInjection(Tool.class);

        //TODO(dwightguth): when we upgrade to Guice 4.0, add
        //binder().requireAtInjectOnConstructors()
    }

}
