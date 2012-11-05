package org.kframework.compile.transformers;


import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
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
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class GenerateSymbolicSyntaxPredicates extends CopyOnWriteTransformer {
  public final static String SymbolicPrefix = "Symbolic";

  public final static boolean hasSymbolicSubsort(String sort) {
    // just for Bool and Int
    return sort.equals("Bool") || sort.equals("Int");
  }

  public final static String getSymbolicSubsort(String sort) {
     assert hasSymbolicSubsort(sort);

     return SymbolicPrefix + sort;
  }

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
      if (!hasSymbolicSubsort(sort))
        return;

      /*
      if (!marked.contains(sort)) {
        marked.add(sort);
        declarePredicate(sort);
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
        if (!hasSymbolicSubsort(sort))
          return symTerms;

        symTerms.add(MetaK.getFreshVar(getSymbolicSubsort(sort)));
        return symTerms;
      }

      TermCons concTerm = (TermCons) MetaK.getTerm(prod);
      for (int i = 0; i < concTerm.getContents().size(); i++) {
        String sort = concTerm.getContents().get(i).getSort();
        if (!hasSymbolicSubsort(sort))
          continue;

        TermCons symTerm = concTerm.shallowCopy();
        List<Term> subterms = new ArrayList<Term>(concTerm.getContents());
        symTerm.setContents(subterms);
        subterms.set(i, MetaK.getFreshVar(getSymbolicSubsort(sort)));

        symTerms.add(symTerm);
      }

      return symTerms;
    }

    private void declarePredicate(String sort) {
      Sort KLabel = new Sort("KLabel");
      List<PriorityBlock> pbs = new LinkedList<PriorityBlock>();
      PriorityBlock pb = new PriorityBlock();
      pbs.add(pb);

      List<Production> prods = new LinkedList<Production>();
      pb.setProductions(prods);

      List<ProductionItem> prodItems = new LinkedList<ProductionItem>();
      prods.add(new Production(KLabel, prodItems));

      prodItems.add(new Terminal("is" + sort));

      result.add(new Syntax(KLabel, pbs));
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

