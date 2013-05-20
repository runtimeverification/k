package org.kframework.compile.transformers;


import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSorts;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.StringBuiltin;
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


public class AddPredicates extends CopyOnWriteTransformer {

    public static final KLabelConstant K2Sort = KLabelConstant.of("K2Sort");

    private static Set<String> tokenNames;

    public class PredicatesVisitor extends BasicVisitor {

        public PredicatesVisitor(String name, DefinitionHelper definitionHelper) {
			super(name, definitionHelper);
		}

		private List<ModuleItem> result = new ArrayList<ModuleItem>();
        private Set<String> lists = new HashSet<String>();

        @Override
        public void visit(Module node) {
            lists.clear();
            super.visit(node);
            if (!lists.isEmpty()) {
                for (String listSort : lists) {
                    Rule rule = new Rule(
                            KApp.of(KLabelConstant.of(predicate(listSort), definitionHelper), new Empty(listSort)),
                            BoolBuiltin.TRUE, definitionHelper);
                    rule.addAttribute(Attribute.PREDICATE);
                    result.add(rule);
                    rule = new Rule(
                            KApp.of(KLabelConstant.KRESULT_PREDICATE, new Empty(listSort)),
                            BoolBuiltin.TRUE, definitionHelper);
                    rule.addAttribute(Attribute.PREDICATE);
                    result.add(rule);
                }
            }
        }

        @Override
        public void visit(Syntax node) {
            String sort = node.getSort().getName();

            if (definitionHelper.isListSort(sort))
                lists.add(sort);

            if (MetaK.isKSort(sort))
                return;
            else
                super.visit(node);
        }

        @Override
        public void visit(Production node) {
            if (node.containsAttribute("bracket"))
                return;
            if (node.containsAttribute("predicate"))
                return;

            if (node.isLexical()) {
                /* predicate definition for token sorts is deferred to each backend */
                return;
            }

            String sort = node.getSort();
            Term term = MetaK.getTerm(node, definitionHelper);

            Term rhs;
            if (node.containsAttribute("function") && node.getArity() > 0)
               rhs = KApp.of(KSymbolicPredicate, term);
            else
               rhs = BoolBuiltin.TRUE;
            Term lhs = KApp.of(KLabelConstant.of(syntaxPredicate(sort), definitionHelper), term);
            Rule rule = new Rule(lhs, rhs, definitionHelper);
            rule.addAttribute(Attribute.PREDICATE);
            result.add(rule);

            // define K2Sort for syntactic production (excluding subsorts)
            if (!node.isSubsort()) {
                lhs = KApp.of(K2Sort, term);
                rhs = StringBuiltin.kAppOf(sort);
                rule = new Rule(lhs, rhs, definitionHelper);
                rule.addAttribute(Attribute.FUNCTION);
                result.add(rule);
            }
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
    public static final KLabelConstant BuiltinPredicate =
            KLabelConstant.of(predicate("Builtin"));
    public static final KLabelConstant VariablePredicate =
            KLabelConstant.of(predicate("Variable"));
    public static final KLabelConstant KSymbolicPredicate =
            KLabelConstant.of(symbolicPredicate("K"));


    public static final String predicate(String sort) {
        return PredicatePrefix + sort;
    }

    public static final String syntaxPredicate(String sort) {
        assert !MetaK.isKSort(sort):
                "invalid syntactic predicate " + predicate(sort) + " for sort " + sort;

        return predicate(sort);
    }

    public static final String symbolicPredicate(String sort) {
        assert AddSymbolicK.allowSymbolic(sort):
                "invalid symbolic predicate " + predicate(SymbolicPredicatePrefix + sort)
                        + " for sort "+ sort;

        return predicate(SymbolicPredicatePrefix + sort);
    }

    @Override
    public ASTNode transform(Definition node) throws TransformerException {
        tokenNames = node.tokenNames();
        return super.transform(node);
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
                retNode.addConstant(KSorts.KLABEL, pred);

                if (AddSymbolicK.allowKSymbolic(sort)) {
                    String symPred = symbolicPredicate(sort);
                    // declare isSymbolicSort predicate as KLabel
                    retNode.addConstant(KSorts.KLABEL, symPred);

                    // define isSymbolicSort predicate as the conjunction of isSort and isSymbolicK
                    Variable var = Variable.getFreshVar("K");
                    Term lhs = KApp.of(KLabelConstant.of(symPred, definitionHelper), var);
                    Term rhs = KApp.of(
                            KLabelConstant.BOOL_ANDTHENBOOL_KLABEL,
                            KApp.of(KLabelConstant.of(pred, definitionHelper), var),
                            KApp.of(KSymbolicPredicate, var));
                    Rule rule = new Rule(lhs, rhs, definitionHelper);
                    rule.addAttribute(Attribute.PREDICATE);
                    retNode.appendModuleItem(rule);

                    String symCtor = AddSymbolicK.symbolicConstructor(sort);
                    var = Variable.getFreshVar(KSorts.KLIST);
                    Term symTerm = KApp.of(KLabelConstant.of(symCtor, definitionHelper), var);

                    // define isSort for symbolic sort constructor symSort
                    lhs = KApp.of(KLabelConstant.of(pred, definitionHelper), symTerm);
                    rule = new Rule(lhs, BoolBuiltin.TRUE, definitionHelper);
                    rule.addAttribute(Attribute.PREDICATE);
                    retNode.appendModuleItem(rule);

                    // define isVariable predicate for symbolic sort constructor symSort
					rule = getIsVariableRule(symTerm, definitionHelper);
                    retNode.appendModuleItem(rule);

                    // define K2Sort function for symbolic sort constructor
                    // symSort
                    lhs = KApp.of(K2Sort, symTerm);
                    rhs = StringBuiltin.kAppOf(sort);
                    rule = new Rule(lhs, rhs, definitionHelper);
                    rule.addAttribute(Attribute.FUNCTION);
                    retNode.appendModuleItem(rule);
                } else if (tokenNames.contains(sort)) {
                    // define isSort predicate for token sorts

                } else if (MetaK.isBuiltinSort(sort)) {
                    Variable var = Variable.getFreshVar(sort);
                    Term lhs = KApp.of(BuiltinPredicate, var);
                    Rule rule = new Rule(lhs, BoolBuiltin.TRUE, definitionHelper);
                    rule.addAttribute(Attribute.PREDICATE);
                    retNode.appendModuleItem(rule);

                    /*
                     * definition for builtins moved in symbolic-k.k
                    lhs = new KApp(K2Sort, var);
                    Term rhs = new Constant("#String", "\"" + sort + "\"");
                    rule = new Rule();
                    rule.setBody(new Rewrite(lhs, rhs));
                    rule.getCellAttributes().getContents().add(Attribute.FUNCTION);
                    retNode.appendModuleItem(rule);
                     */
                }
            }
        }

        PredicatesVisitor mv = new PredicatesVisitor("PredicatesVisitor", definitionHelper);
        node.accept(mv);
        retNode.getItems().addAll(mv.getResult());

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

	public static Rule getIsVariableRule(Term symTerm, DefinitionHelper definitionHelper) {
		Term lhs;
		Rule rule;
		if (!MetaK.isComputationSort(symTerm.getSort())) {
			symTerm = KApp.of(new KInjectedLabel(symTerm));
		}

		lhs = KApp.of(VariablePredicate, symTerm);
		rule = new Rule(lhs, BoolBuiltin.TRUE, definitionHelper);
		rule.addAttribute(Attribute.PREDICATE);
		return rule;
	}

	public AddPredicates(DefinitionHelper definitionHelper) {
        super("Add syntax and symbolic predicates", definitionHelper);
    }

}
