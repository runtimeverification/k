package org.kframework.compile.transformers;


import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.KApp;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class GenerateSymbolicSyntaxPredicates extends CopyOnWriteTransformer {

  public class SymbolicSyntaxPredicatesVisitor extends BasicVisitor {
    List<ModuleItem> result = new ArrayList<ModuleItem>();
    Set<String> marked = new HashSet<String>();

    @Override
    public void visit(Module node) {
      super.visit(node);
    }

    @Override
    public void visit(Syntax node) {
      String sort = node.getSort().getName();
      if (MetaK.isKSort(sort))
        return;

      super.visit(node);
    }

    @Override
    public void visit(Production node) {
      if (node.getAttributes().containsKey("bracket")) return;
      if (node.getAttributes().containsKey("predicate")) return;

      String sort = node.getSort();
      if (!AddSymbolicSorts.hasSymbolicSubsort(sort))
        return;

      /*
      if (!marked.contains(sort)) {
        marked.add(sort);
      }
      */

      System.err.println(">>> " + sort + " ::= " + node);
      for (Term symTerm : makeSymbolicTerms(node)) {
        Rule rule = new Rule();
        rule.setBody(new Rewrite(
            new KApp(new Constant("KLabel", "is" + sort), symTerm),
            new Constant("#Bool", "true")));
        rule.getAttributes().getContents().add(new Attribute("predicate", ""));
        result.add(rule);
      }
    }

    private List<Term> makeSymbolicTerms(Production prod) {
      List<Term> symTerms = new ArrayList<Term>();

      if (prod.isSubsort()) {
        String sort = ((Sort) prod.getItems().get(0)).getName();
        if (!AddSymbolicSorts.hasSymbolicSubsort(sort))
          return symTerms;

        String symSort = AddSymbolicSorts.getSymbolicSubsort(sort);
        symTerms.add(MetaK.getFreshVar(symSort));
        return symTerms;
      }

      TermCons concTerm = (TermCons) MetaK.getTerm(prod);
      for (int i = 0; i < concTerm.getContents().size(); i++) {
        String sort = concTerm.getContents().get(i).getSort();
        if (!AddSymbolicSorts.hasSymbolicSubsort(sort))
          continue;

        TermCons symTerm = concTerm.shallowCopy();
        List<Term> subterms = new ArrayList<Term>(concTerm.getContents());
        symTerm.setContents(subterms);
          String symSort = AddSymbolicSorts.getSymbolicSubsort(sort);
          subterms.set(i, MetaK.getFreshVar(symSort));

        symTerms.add(symTerm);
      }

      return symTerms;
    }

    @Override
    public void visit(Rule node) {
    }

    @Override
    public void visit(Context node) {
    }

    @Override
    public void visit(Configuration node) {
    }

    public List<ModuleItem> getResult() {
      return result;
    }
  }


  @Override
  public ASTNode transform(Module node) throws TransformerException {
    SymbolicSyntaxPredicatesVisitor mv = new SymbolicSyntaxPredicatesVisitor();
    node.accept(mv);

    List<ModuleItem> preds = mv.getResult();
    if (preds.isEmpty())
      return node;

    node = node.shallowCopy();
    List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
    node.setItems(items);
    items.addAll(preds);

    return node;
  }

  public GenerateSymbolicSyntaxPredicates() {
    super("Generate syntax predicates");
  }

}

