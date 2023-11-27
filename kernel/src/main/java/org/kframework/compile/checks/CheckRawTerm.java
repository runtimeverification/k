package org.kframework.compile.checks;

import java.util.Set;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;

public record CheckRawTerm(Set<KEMException> errors) {
  public void check(Sentence s) {}
}
