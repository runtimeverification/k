// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;
import org.kframework.attributes.Source;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.utils.errorsystem.KEMException;

/** Created by dwightguth on 4/20/15. */
public record ParseCache(Module module, boolean strict, Map<String, ParsedSentence> cache)
    implements Serializable {
  public record ParsedSentence(
      K parse,
      Set<KEMException> warnings,
      Set<KEMException> errors,
      int startLine,
      int startColumn,
      Source source)
      implements Serializable {}
}
