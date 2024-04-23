// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kil.loader;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.inject.Inject;
import java.io.Serializable;
import org.kframework.attributes.Att;
import org.kframework.kil.Production;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.inject.RequestScoped;

@RequestScoped
public class Context implements Serializable {

  @Inject
  public Context() {}

  /**
   * Represents a map from all Klabels and group(_) tags in string representation to sets of
   * corresponding productions.
   */
  public SetMultimap<String, Production> tags = HashMultimap.create();

  // TODO(dwightguth): remove these fields and replace with injected dependencies
  @Deprecated @Inject public transient GlobalOptions globalOptions;
  public KompileOptions kompileOptions;

  public void addProduction(Production p) {
    if (p.getKLabel(false) != null) {
      tags.put(p.getKLabel(false), p);
    } else if (p.getAttributes().contains(Att.BRACKET())) {
      tags.put(p.getBracketLabel(false), p);
    }
    if (p.getAttributes().contains(Att.GROUP())) {
      String groups = p.getAttributes().get(Att.GROUP());
      if (!groups.matches("\\s*[a-z][a-zA-Z0-9-]*\\s*(,\\s*[a-z][a-zA-Z0-9-]*\\s*)*")) {
        throw KEMException.compilerError(
            "group(_) attribute expects a comma separated list of "
                + "groups, each of which consists of a lower case letter followed by any "
                + "number of alphanumeric or '-' characters.",
            p);
      }
      for (String group : groups.split("\\s*,\\s*")) {
        tags.put(group, p);
      }
    }
  }
}
