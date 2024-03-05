// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;

import java.util.Set;
import org.kframework.definition.Definition;
import org.kframework.definition.Import;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import scala.collection.concurrent.Map;
import scala.collection.concurrent.TrieMap;

public abstract class KorePipelineStage {
  public String name;
  public Set<String> dependencies;

  public KorePipelineStage() {
    this("");
  }

  public KorePipelineStage(String name) {
    this(name, Set.of());
  }

  public KorePipelineStage(String name, Set<String> dependencies) {
    this.name = name;
    this.dependencies = dependencies;
  }

  /**
   * Transform a definition.
   *
   * <p>Applies the module transformer to all modules in the definition. Implementations may want to
   * override this in order to retrieve some information from the definition before processing, they
   * can call super.apply(d) after doing so.
   */
  public Definition apply(Definition d) {
    return new Definition(
        recursiveModuleApply(d.mainModule()),
        stream(d.entryModules()).map(this::recursiveModuleApply).collect(toSet()),
        d.att());
  }

  /**
   * Transform a module.
   *
   * <p>This method should assume that all of the modules in the imports are already processed.
   */
  public Module apply(Module m) {
    return new Module(
        m.name(),
        m.imports(),
        stream(m.localSentences()).map(this::apply).collect(toSet()),
        m.att());
  }

  /** Transform a sentence. */
  public Sentence apply(Sentence s) {
    return s;
  }

  /**
   * Transform a module recursively on all of its imports.
   *
   * <p>It's likely that if one wants to apply an implementation of this stage to a Module instead
   * of a Definition, they will want to call this method instead of the raw apply(Module) method.
   */
  private Map<Module, Module> cachedModules = new TrieMap<>();

  public final Module recursiveModuleApply(Module m) {
    return cachedModules.getOrElseUpdate(
        m,
        () -> {
          scala.collection.Set<Import> newImports =
              stream(m.imports())
                  .map(i -> new Import(recursiveModuleApply(i.module()), i.isPublic()))
                  .collect(toSet());
          if (!newImports.equals(m.imports())) {
            return apply(new Module(m.name(), newImports, m.localSentences(), m.att()));
          } else {
            return apply(m);
          }
        });
  }
}
