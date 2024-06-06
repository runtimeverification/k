// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import org.kframework.attributes.Att;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.kore.ADT.KVariable;
import org.kframework.parser.Constant;

/**
 * A type representing a particular variable. Specifically, either
 *
 * <ul>
 *   <li>Named, which just records the variable's name
 *   <li>Anon, which wraps the particular Constant of an anonymous variable in order to provide it
 *       reference semantics (lest all vars named "_" compare equal).
 * </ul>
 */
public sealed interface VariableId {
  static VariableId apply(Constant var) {
    if (ResolveAnonVar.isAnonVarOrNamedAnonVar(new KVariable(var.value(), Att.empty()))) {
      return new Anon(var);
    }
    return new Named(var.value());
  }

  record Named(String name) implements VariableId {}

  record Anon(Constant constant) implements VariableId {
    @Override
    public boolean equals(Object o) {
      if (o instanceof Anon a) {
        return this.constant == a.constant;
      }
      return false;
    }

    @Override
    public int hashCode() {
      return System.identityHashCode(constant);
    }
  }
}
