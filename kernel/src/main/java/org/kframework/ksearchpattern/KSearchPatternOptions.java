// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.ksearchpattern;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.DefinitionLoadingOptions;

import java.util.List;

/**
 * JCommander options for k-compile-search-pattern.
 */

@RequestScoped
public class KSearchPatternOptions {

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

    @Parameter(description="<file>")
    private List<String> parameters;

    public String pattern() {
      return parameters.get(0);
    }
}
