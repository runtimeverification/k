// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import org.kframework.main.FrontEnd;
import org.kframework.main.Tool;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.general.GlobalSettings;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;

public class CommonModule extends AbstractModule {

    @Override
    protected void configure() {
        requestStaticInjection(Stopwatch.class);
        requestStaticInjection(GlobalSettings.class);
        requestStaticInjection(BinaryLoader.class);
        requestStaticInjection(Tool.class);
    }

    @Provides
    Tool tool(FrontEnd frontend) {
        return frontend.tool();
    }

}
