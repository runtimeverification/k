// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kserver;

import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;

@RequestScoped
public class KServerOptions {

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @Parameter(names={"--port", "-p"}, description="The port to start the server on.")
    public int port = 2113;
}
