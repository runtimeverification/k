// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import java.util.stream.Stream;
import org.kframework.attributes.Att;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kore.K;
import org.kframework.kore.KRewrite;

/**
 * Apply the configuration concretization process. The implicit {@code <k>} cell is added by another
 * stage, AddImplicitComputationCell.
 *
 * <p>The input may freely use various configuration abstractions and Full K flexibilites. See
 * {@link IncompleteCellUtils} for a description of the expected term structure. The output will
 * represent cells in strict accordance with their declared fixed-arity productions.
 *
 * <p>This is a simple composition of the {@link AddTopCellToRules}, {@link AddParentCells}, {@link
 * CloseCells}, and {@link SortCells} passes, see their documentation for details on the
 * transformations.
 */
public class ConcretizeCells {
  final ConfigurationInfo configurationInfo;
  final LabelInfo labelInfo;
  final SortInfo sortInfo;
  final Module module;

  final AddParentCells addParentCells;
  final CloseCells closeCells;
  final SortCells sortCells;
  private final AddTopCellToRules addRootCell;

  public static Definition transformDefinition(Definition input) {
    ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(input.mainModule());
    LabelInfo labelInfo = new LabelInfoFromModule(input.mainModule());
    SortInfo sortInfo = SortInfo.fromModule(input.mainModule());
    return DefinitionTransformer.fromSentenceTransformer(
            new ConcretizeCells(configInfo, labelInfo, sortInfo, input.mainModule())::concretize,
            "concretizing configuration")
        .apply(input);
  }

  public ConcretizeCells(
      ConfigurationInfo configurationInfo, LabelInfo labelInfo, SortInfo sortInfo, Module module) {
    this.configurationInfo = configurationInfo;
    this.labelInfo = labelInfo;
    this.sortInfo = sortInfo;
    this.module = module;
    addRootCell = new AddTopCellToRules(configurationInfo, labelInfo);
    addParentCells = new AddParentCells(configurationInfo, labelInfo);
    closeCells = new CloseCells(configurationInfo, sortInfo, labelInfo);
    sortCells = new SortCells(configurationInfo, labelInfo, module);
  }

  public Sentence concretize(Module m, Sentence s) {
    if (s instanceof Claim c && !hasCells(c.body())) {
      return s;
    }
    s = addRootCell.addImplicitCells(s, m);
    s = addParentCells.concretize(s);
    s = closeCells.close(s);

    s = sortCells.preprocess(s);
    s = sortCells.sortCells(s);
    s = sortCells.postprocess(s);
    return s;
  }

  public static boolean hasCells(K item) {
    if (IncompleteCellUtils.flattenCells(item).stream()
        .anyMatch(
            k -> k.att().get(Att.PRODUCTION(), Production.class).att().contains(Att.CELL()))) {
      return true;
    }

    if (item instanceof KRewrite rew) {
      return Stream.concat(
              IncompleteCellUtils.flattenCells(rew.left()).stream(),
              IncompleteCellUtils.flattenCells(rew.right()).stream())
          .anyMatch(ConcretizeCells::hasCells);
    }

    return false;
  }
}
