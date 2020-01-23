// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.parser.concrete2kore.ParseCache;

import javax.annotation.Nullable;
import java.io.Serializable;
import java.util.Collections;
import java.util.Map;

/**
 * Represents compiled definition, parse cache and extended definitions derived from this base definition at runtime.
 *
 * @author Denis Bogdanas
 * Created on 05-Nov-19.
 */
public class DefinitionAndCache implements Serializable {
    public final @Nullable CompiledDefinition compiledDefinition;
    public final Map<String, ParseCache> parseCaches;

    public DefinitionAndCache(CompiledDefinition compiledDefinition,
                              Map<String, ParseCache> parseCaches) {
        this.compiledDefinition = compiledDefinition;
        this.parseCaches = Collections.synchronizedMap(parseCaches);
    }
}
