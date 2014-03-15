package org.kframework.parser;

import com.beust.jcommander.Parameter;

public final class ExperimentalParserOptions {

    @Parameter(names="--Xfast-kast", description="Using the (experimental) faster C SDF parser.")
    public boolean fastKast = false;
}
