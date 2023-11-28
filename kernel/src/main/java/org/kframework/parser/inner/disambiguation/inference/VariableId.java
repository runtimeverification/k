package org.kframework.parser.inner.disambiguation.inference;

import org.kframework.attributes.Att;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.kore.ADT.KVariable;
import org.kframework.parser.Constant;

public sealed interface VariableId {
  static VariableId apply(Constant var) {
    if (ResolveAnonVar.isAnonVarOrNamedAnonVar(new KVariable(var.value(), Att.empty()))) {
      return new Anon(var);
    }
    return new Named(var.value());
  }

  record Named(String name) implements VariableId {}

  final class Anon implements VariableId {
    private final Constant constant;

    public Anon(Constant constant) {
      this.constant = constant;
    }

    public Constant constant() {
      return constant;
    }

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
