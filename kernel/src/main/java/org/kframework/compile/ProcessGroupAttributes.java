// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Syntax;
import org.kframework.utils.errorsystem.KEMException;
import scala.util.Either;

/**
 * A pass which handles all "user group" attributes. Specifically, the attribute
 * [group(att1,...,attN)] is replaced with the underlying attributes [att1,...,attN].
 */
public class ProcessGroupAttributes {
  public static Att getProcessedAtt(Att att, HasLocation node) {
    Either<String, Att> newAttOrError = att.withGroupAttAsUserGroups();
    if (newAttOrError.isLeft()) {
      throw KEMException.compilerError(newAttOrError.left().get(), node);
    }
    Att newAtt = newAttOrError.right().get();
    return newAtt;
  }

  public static void apply(Module m) {
    m.setAttributes(getProcessedAtt(m.getAttributes(), m));
    m.getItems().stream()
        .filter((modItem) -> modItem instanceof Syntax)
        .flatMap((s) -> ((Syntax) s).getPriorityBlocks().stream())
        .flatMap((pb) -> pb.getProductions().stream())
        .forEach((p) -> p.setAttributes(getProcessedAtt(p.getAttributes(), p)));
  }

  public static void apply(Definition d) {
    d.getItems().stream()
        .filter((item) -> item instanceof Module)
        .forEach((m) -> apply((Module) m));
  }
}
