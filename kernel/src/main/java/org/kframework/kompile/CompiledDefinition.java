// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.attributes.Source;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kore.K;

import java.util.function.BiFunction;

/**
 * Created by dwightguth on 4/17/15.
 */

public class CompiledDefinition {
    private final Module compiledExecutionModule;
    private final Definition parsedDefinition;
    private final BiFunction<String, Source, K> programParser;

    public CompiledDefinition(Module compiledExecutionModule, Definition parsedDefinition, BiFunction<String, Source, K> programParser) {
        this.compiledExecutionModule = compiledExecutionModule;
        this.parsedDefinition = parsedDefinition;
        this.programParser = programParser;
    }

    /**
     * A function that takes a string and the source of that string and parses it as a program into KAST.
     */
    public BiFunction<String, Source, K> getProgramParser() {
        return programParser;
    }

    /**
     * The parsed but uncompiled definition
     */
    public Definition getParsedDefinition() {
        return parsedDefinition;
    }

    /**
     * A module containing the compiled definition
     */
    public Module getCompiledExecutionModule() {
        return compiledExecutionModule;
    }
}