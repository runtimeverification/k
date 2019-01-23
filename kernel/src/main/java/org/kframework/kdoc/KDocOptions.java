// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kdoc;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.kframework.backend.Backends;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.OuterParsingOptions;

@RequestScoped
public class KDocOptions {

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @Parameter(names="--format", description="Choose a format. <format> is one of [pdf|latex|html|unparse|doc|unflatten]. Each generates a document from the given K definition.")
    public String format = Backends.PDF;

    @ParametersDelegate
    public OuterParsingOptions outerParsing = new OuterParsingOptions();

}
