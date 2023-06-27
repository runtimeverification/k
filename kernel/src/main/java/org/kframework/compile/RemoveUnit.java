// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.*;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Stream;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

public class RemoveUnit {

  private Module m;

  public Module apply(Module module) {
    m = module;
    return Module(module.name(), module.imports(), stream(module.localSentences()).flatMap(this::gen).collect(Collections.toSet()), module.att());
  }

  private Stream<Sentence> gen(Sentence s) {
    if (!(s instanceof Rule)) {
      return Stream.of(s);
    }
    Rule r = (Rule)s;
    K body = flattenLists(r.body());
    K requires = flattenLists(r.requires());
    K ensures = flattenLists(r.ensures());
    return Stream.of(Rule(body, requires, ensures, r.att()));
  }

  private K flattenLists(K k) {
    return new TransformK() {
      @Override
      public K apply(KApply k) {
        Att att = m.attributesFor().getOrElse(k.klabel(), () -> Att.empty());

        // Ignore optional cells, which have a unit attribute but no assoc
        if (   att.contains(Att.CELL())
            && att.contains(Att.MULTIPLICITY())
            && att.get(Att.MULTIPLICITY()).equals("?")) {
          return super.apply(k);
        }

        if (att.contains(Att.UNIT())) {
          if (!att.contains(Att.ASSOC())) {
            throw KEMException.internalError("unimplemented case in RemoveUnit: unit but no assoc");
          }
          return Assoc.flatten(k.klabel(), k.items(), m).stream().reduce((k1, k2) -> KApply(k.klabel(), k1, k2)).orElse(KApply(KLabel(att.get(Att.UNIT()))));
        }
        return super.apply(k);
      }
    }.apply(k);
  }
}
