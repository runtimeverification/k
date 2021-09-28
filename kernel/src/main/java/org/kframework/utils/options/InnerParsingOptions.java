// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

import java.io.Serializable;

/**
 * Provides the options needed for tools to perform inner parsing of definitions from source.
 *
 * Used currently by kompile, and kprove.
 */
public class InnerParsingOptions implements Serializable {

    public InnerParsingOptions() {}

    @Inject
    public InnerParsingOptions(Void v) {}

    @Parameter(names="--profile-rule-parsing", description="Generate time in milliseconds to parse each rule in the semantics.")
    public String profileRules;
}
