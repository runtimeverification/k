// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.definition.Definition;
import org.kframework.parser.concrete2kore.ParseCache;

import javax.annotation.Nullable;
import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

/**
 * Represents compiled definition, parse cache and extended definitions derived from this base definition at runtime.
 * All fields of this class must be serialized/deserialized together, because they share a lot of inner objects.
 *
 * @author Denis Bogdanas
 * Created on 05-Nov-19.
 */
public class DefinitionAndCache implements Serializable {
    public final @Nullable CompiledDefinition compiledDefinition;
    public final Map<String, ParseCache> parseCaches;

    //Map from raw to compiled definitions extended at runtime, based on compiledDefinition.
    public final Map<Definition, Definition> extendedDefinitionsCache = Collections.synchronizedMap(new HashMap<>());

    public DefinitionAndCache(CompiledDefinition compiledDefinition,
                              Map<String, ParseCache> parseCaches) {
        this.compiledDefinition = compiledDefinition;
        this.parseCaches = Collections.synchronizedMap(parseCaches);
    }
}
