// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kil.loader;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.inject.Inject;
import org.kframework.attributes.Att;
import org.kframework.attributes.Att.Key;
import org.kframework.kil.Production;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.inject.RequestScoped;
import scala.Tuple2;

import java.io.Serializable;

import static org.kframework.Collections.*;

@RequestScoped
public class Context implements Serializable {

    /**
     * Represents a map from all Klabels or attributes in string representation
     * to sets of corresponding productions.
     */
    public SetMultimap<String, Production> tags = HashMultimap.create();

    // TODO(dwightguth): remove these fields and replace with injected dependencies
    @Deprecated @Inject public transient GlobalOptions globalOptions;
    public KompileOptions kompileOptions;

    public void addProduction(Production p) {
        if (p.containsAttribute(Att.GROUP())) {
            throw new AssertionError(
                    "Must call ExpandGroupAttribute.apply(Definition) before creating a Context.");
        }

        if (p.getKLabel(false) != null) {
            tags.put(p.getKLabel(false), p);
        } else if (p.getAttributes().contains(Att.BRACKET())) {
            tags.put(p.getBracketLabel(false), p);
        }
        for (Tuple2<Att.Key, String> a : iterable(p.getAttributes().att().keys())) {
            tags.put(a._1.key(), p);
        }
    }
}
