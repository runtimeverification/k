// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import org.kframework.TopologicalSort;
import org.kframework.definition.Definition;
import scala.Tuple2;

public class KorePipeline {
  private Set<KorePipelineStage> stages;

  public KorePipeline() {
    this.stages = new HashSet<>();
  }

  /** Apply the pipeline to a definition. */
  public Definition apply(Definition d) {
    List<KorePipelineStage> resolvedPipeline = resolveDependencies();

    for (KorePipelineStage stage : resolvedPipeline) {
      d = stage.apply(d);
    }

    return d;
  }

  /** Add a stage to this pipeline */
  public void registerStage(KorePipelineStage stage) {
    stages.add(stage);
  }

  /** Add a collection of stages to this pipeline */
  public void registerStages(Collection<KorePipelineStage> stagesToAdd) {
    stagesToAdd.stream().forEach(this::registerStage);
  }

  /** Schedule all of the stages according to their dependencies. */
  private List<KorePipelineStage> resolveDependencies() {
    // To ensure the resulting list contains all of the stages in the
    // pipeline, a unit stage is declared here that every stage depends
    // on, so stages with no dependencies can exist in the set of edges
    // for the topological sort.
    KorePipelineStage unitStage =
        new KorePipelineStage() {
          public Definition apply(Definition d) {
            return d;
          }
        };

    // Make the edges of the dependency graph
    Set<Tuple2<KorePipelineStage, KorePipelineStage>> edges = new HashSet<>();
    for (KorePipelineStage stage : stages) {
      edges.add(new Tuple2(unitStage, stage));
      for (String depName : stage.dependencies) {
        Optional<KorePipelineStage> depReference =
            stages.stream().filter(p -> p.name == depName).findFirst();
        if (depReference.isPresent()) {
          edges.add(new Tuple2(depReference.get(), stage));
        }
      }
    }

    return stream(TopologicalSort.tsort(immutable(edges))).collect(Collectors.toList());
  }
}
