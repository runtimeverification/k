// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.kdep;

import com.beust.jcommander.ParametersDelegate;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.OuterParsingOptions;

/**
 * JCommander options for kdep. Essentially, this should contain all the kompile options needed in order to decide what
 * files get slurped by the outer parser.
 */

@RequestScoped
public class KDepOptions {

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public OuterParsingOptions outerParsing = new OuterParsingOptions();
}
