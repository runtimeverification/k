package org.kframework.compile.transformers;


import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.ListOfK;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


public class AddSyntaxPredicates extends CopyOnWriteTransformer {

    public static final String syntaxPredicatePrefix = "is";

    public static final String syntaxPredicate (String sort) {
        //assert !MetaK.isKSort(sort) && !MetaK.isBuiltinSort(sort);
        assert !MetaK.isKSort(sort);

        return syntaxPredicatePrefix + sort;
    }

    public class SyntaxPredicatesVisitor extends BasicVisitor {

        private List<ModuleItem> result = new ArrayList<ModuleItem>();
        private Set<String> lists = new HashSet<String>();

        @Override
        public void visit(Module node) {
            lists.clear();
            super.visit(node);
            if (!lists.isEmpty()) {
                for (String listSort : lists) {
                    Rule rule = new Rule();
                    rule.setBody(new Rewrite(
                            new KApp(new Constant("KLabel", "is" + listSort),
                                    new Empty(listSort)),
                            new Constant("#Bool", "true")));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    result.add(rule);
                    rule = new Rule();
                    rule.setBody(new Rewrite(
                            new KApp(new Constant("KLabel", "isKResult"),
                                    new Empty(listSort)),
                            new Constant("#Bool", "true")));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    result.add(rule);
                }
            }
        }

        @Override
        public void visit(Syntax node) {
            String sort = node.getSort().getName();

            if (DefinitionHelper.isListSort(sort))
                lists.add(sort);

            if (MetaK.isKSort(sort))
                return;
            else
                super.visit(node);
        }

        @Override
        public void visit(Production node) {
            if (node.getAttributes().containsKey("bracket"))
                return;
            if (node.getAttributes().containsKey("predicate"))
                return;

            String sort = node.getSort();
            Term term = MetaK.getTerm(node);
            Term rhs;
            if (node.getAttributes().containsKey("function") &&
                    node.getArity() > 0)
               rhs = new KApp(AddSymbolicK.isSymbolicK, term);
            else
               rhs = new Constant("#Bool", "true");

            Constant ct = new Constant("KLabel", syntaxPredicate(sort));
            Term lhs = new KApp(ct, term);
            Rule rule = new Rule();
            rule.setBody(new Rewrite(lhs, rhs));
            rule.getAttributes().getContents().add(new Attribute("predicate", ""));
            result.add(rule);
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
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));


        for (String sort : node.getAllSorts()) {
            if (!MetaK.isKSort(sort)) {
                String pred = syntaxPredicate(sort);
                retNode.addConstant("KLabel", pred);

                if (AddSymbolicK.allowKSymbolic(sort)) {
                    String symPred = AddSymbolicK.symbolicPredicate(sort);
                    retNode.addConstant("KLabel", symPred);

                    Variable var = MetaK.getFreshVar("K");
                    Term lhs = new KApp(new Constant("KLabel", symPred), var);
                    ListOfK list = new ListOfK();
                    Constant andKLbl = new Constant("KLabel", "'_andThenBool_");
                    Term rhs = new KApp(andKLbl, list);
                    list.getContents().add(new KApp(new Constant("KLabel", pred), var));
                    list.getContents().add(new KApp(AddSymbolicK.isSymbolicK, var));
                    Rule rule = new Rule();
                    rule.setBody(new Rewrite(lhs, rhs));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    retNode.appendModuleItem(rule);
                }

                if (MetaK.isBuiltinSort(sort)) {
                    Variable var = MetaK.getFreshVar(sort);
                    Term lhs = new KApp(AddSymbolicK.isSymbolicK, var);
                    Term rhs = new Constant("#Bool", "false");

                    Rule rule = new Rule();
                    rule.setBody(new Rewrite(lhs, rhs));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    retNode.appendModuleItem(rule);
                }
            }
        }

        SyntaxPredicatesVisitor mv = new SyntaxPredicatesVisitor();
        node.accept(mv);
        retNode.getItems().addAll(mv.getResult());

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

    public AddSyntaxPredicates() {
        super("Add syntax and symbolic predicates");
    }

}
