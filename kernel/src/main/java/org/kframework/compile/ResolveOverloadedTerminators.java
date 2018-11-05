// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.kore.*;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

public class ResolveOverloadedTerminators {

    private final Module mod;
    private final Set<KLabel> overloadedProds;

    public ResolveOverloadedTerminators(Module mod) {
        this.mod = mod;
        overloadedProds = stream(mod.overloads().elements()).filter(p -> p.klabel().isDefined()).map(p -> p.klabel().get()).collect(Collectors.toSet());
    }

    public K resolve(K term) {
        return new TransformK() {
            @Override
            public K apply(KApply kapp) {
                if (overloadedProds.contains(kapp.klabel()) && kapp.items().isEmpty()) {
                    Production prod = mod.productionsFor().apply(kapp.klabel()).head();
                    Set<Production> candidates = stream(mod.overloads().elements()).filter(p -> p.klabel().isDefined() && p.att().get("klabel").equals(prod.att().get("klabel"))).collect(Collectors.toSet());
                    candidates = mod.overloads().minimal(candidates);
                    if (candidates.size() != 1) {
                        throw KEMException.compilerError("Overloaded term does not have a least sort. Possible sorts: " + candidates, kapp);
                    }
                    return KApply(candidates.iterator().next().klabel().get(), KList(kapp.items()), kapp.att());
                }
                return super.apply(kapp);
            }
        }.apply(term);
    }
}
