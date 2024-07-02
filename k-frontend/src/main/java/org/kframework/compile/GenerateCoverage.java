// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.builtin.Sorts;
import org.kframework.definition.*;
import org.kframework.definition.Import;
import org.kframework.definition.Module;
import org.kframework.definition.RuleOrClaim;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.utils.StringUtil;
import org.kframework.utils.file.FileUtil;
import scala.Function1;
import scala.collection.Set;

public class GenerateCoverage {

  public static Definition gen(Definition definition, FileUtil files) {
    Module m = definition.mainModule();
    Function1<Definition, Definition> addIOModule =
        DefinitionTransformer.from(
            mod -> {
              if (mod.equals(m)) {
                return Module(
                    m.name(),
                    m.imports().$bar(Set(Import(definition.getModule("K-IO").get(), true))).toSet(),
                    m.localSentences(),
                    m.att());
              } else {
                return mod;
              }
            },
            "Add K-IO Module for coverage instrumentation");
    Function1<Definition, Definition> addInstrumentation =
        d ->
            DefinitionTransformer.fromRuleBodyTransformerWithRule(
                    (r, body) -> gen(r, body, d.mainModule(), files),
                    "generate coverage instrumentation")
                .apply(d);
    return addIOModule.andThen(addInstrumentation).apply(definition);
  }

  private static K gen(RuleOrClaim r, K body, Module mod, FileUtil files) {
    if (r.att().getOptional(Att.SOURCE(), Source.class).isEmpty()) {
      return body;
    }
    K left = RewriteToTop.toLeft(body);
    K right = RewriteToTop.toRight(body);
    String id = r.att().get(Att.UNIQUE_ID());

    if (ExpandMacros.isMacro(r)) {
      // handled by macro expander
      return body;
    }

    AddSortInjections inj = new AddSortInjections(mod);

    Sort s = inj.topSort(body);

    K k =
        KApply(
            KLabel("sideEffect:" + s.toString()),
            KApply(
                KLabel("#logToFile"),
                KToken(
                    StringUtil.enquoteKString(
                        files.resolveKompiled("coverage.txt").getAbsolutePath()),
                    Sorts.String()),
                KToken(StringUtil.enquoteKString(id + '\n'), Sorts.String())),
            right);

    return KRewrite(left, k);
  }
}
