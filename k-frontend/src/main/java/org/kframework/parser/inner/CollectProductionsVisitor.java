// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner;

import java.util.List;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kore.Sort;

public class CollectProductionsVisitor {
  private final Context context;

  public CollectProductionsVisitor(Context context) {
    this.context = context;
  }

  private String moduleName;
  private Sort sort;
  private List<Sort> params;

  public void visit(Module mod) {
    this.moduleName = mod.getName();
    mod.getItems()
        .forEach(
            mi -> {
              if (mi instanceof Syntax) visit((Syntax) mi);
            });
  }

  public void visit(Syntax syntax) {
    this.sort = syntax.getDeclaredSort().getRealSort();
    this.params = syntax.getParams();
    syntax.getPriorityBlocks().forEach(pb -> pb.getProductions().forEach(this::visit));
  }

  public void visit(Production node) {
    node.setSort(sort);
    node.setOwnerModuleName(moduleName);
    node.setParams(params);
    context.addProduction(node);
  }

  public void visit(Definition def) {
    def.getItems()
        .forEach(
            di -> {
              if (di instanceof Module) visit((Module) di);
            });
  }
}
