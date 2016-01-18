// Copyright (c) 2016 K Team. All Rights Reserved.

package org.kframework.kore.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.KToken;
import org.kframework.kore.SortedADT;
import org.kframework.kore.TransformK;
import scala.Option;

import java.util.function.BiFunction;

/**
 * Used by logik to down Variables represented as tokens to true Variables
 * Should be removed once we have true meta-level.
 */
public class KTokenVariablesToTrueVariables implements BiFunction<Module, K, K> {
    @Override
    public K apply(Module module, K k) {
        return new TransformK() {
            public K apply(KToken t) {
                Option<Att> attOption = module.attForSort().get(t.sort());
                if(attOption.isDefined() && attOption.get().contains(Att.variable())) {
                    return new SortedADT.SortedKVariable(t.s(), t.att().add(Att.sort(), t.sort().name()));
                } else {
                    return t;
                }
            }
        }.apply(k);
    }
}
