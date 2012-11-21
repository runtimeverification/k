package org.kframework.compile.transformers;


import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


public class AddPredicates extends CopyOnWriteTransformer {

    public class PredicatesVisitor extends BasicVisitor {

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
               rhs = new KApp(KSymbolicPredicate, term);
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


    private static final String PredicatePrefix = "is";
    private static final String SymbolicPredicatePrefix = "Symbolic";
    public static final Constant BuiltinPredicate =
            new Constant("KLabel", predicate("Builtin"));
    public static final Constant VariablePredicate =
            new Constant("KLabel", predicate("Variable"));
    public static final Constant KSymbolicPredicate =
            new Constant("KLabel", symbolicPredicate("K"));


    public static final String predicate(String sort) {
        return PredicatePrefix + sort;
    }

    public static final String syntaxPredicate(String sort) {
        assert !MetaK.isKSort(sort);

        return predicate(sort);
    }

    public static final String symbolicPredicate(String sort) {
        assert AddSymbolicK.allowSymbolic(sort);

        return predicate(SymbolicPredicatePrefix + sort);
    }


    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        // declare isBuiltin predicate as KLabel
        retNode.addConstant(BuiltinPredicate);
        // declare isSymbolicK predicate as KLabel
        retNode.addConstant(KSymbolicPredicate);

        for (String sort : node.getAllSorts()) {
            if (!MetaK.isKSort(sort)) {
                String pred = syntaxPredicate(sort);
                // declare isSort predicate as KLabel
                retNode.addConstant("KLabel", pred);

                if (AddSymbolicK.allowKSymbolic(sort)) {
                    String symPred = symbolicPredicate(sort);
                    // declare isSymbolicSort predicate as KLabel
                    retNode.addConstant("KLabel", symPred);

                    // define isSymbolicSort predicate
                    Variable var = MetaK.getFreshVar("K");
                    Term lhs = new KApp(new Constant("KLabel", symPred), var);
                    ListOfK list = new ListOfK();
                    Constant andKLbl = new Constant("KLabel", "'_andThenBool_");
                    Term rhs = new KApp(andKLbl, list);
                    list.getContents().add(new KApp(new Constant("KLabel", pred), var));
                    list.getContents().add(new KApp(KSymbolicPredicate, var));
                    Rule rule = new Rule();
                    rule.setBody(new Rewrite(lhs, rhs));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    retNode.appendModuleItem(rule);

                    // define isVariable predicate
                    String symCtor = AddSymbolicK.symbolicConstructor(sort);
                    var = MetaK.getFreshVar("List{K}");
                    Term symTerm = new KApp(new Constant("KLabel", symCtor), var);
                    lhs = new KApp(VariablePredicate, symTerm);
                    rhs = new Constant("#Bool", "true");
                    rule = new Rule();
                    rule.setBody(new Rewrite(lhs, rhs));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    retNode.appendModuleItem(rule);
                } else if (MetaK.isBuiltinSort(sort)) {
                    Variable var = MetaK.getFreshVar(sort);
                    Term lhs = new KApp(BuiltinPredicate, var);
                    Term rhs = new Constant("#Bool", "true");

                    Rule rule = new Rule();
                    rule.setBody(new Rewrite(lhs, rhs));
                    rule.getAttributes().getContents().add(new Attribute("predicate", ""));
                    retNode.appendModuleItem(rule);
                }
            }
        }

        PredicatesVisitor mv = new PredicatesVisitor();
        node.accept(mv);
        retNode.getItems().addAll(mv.getResult());

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

    public AddPredicates() {
        super("Add syntax and symbolic predicates");
    }

}
