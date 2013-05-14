package org.kframework.compile.transformers;

import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;


/*
 * User: Andrei Stefanescu
 * Date: 11/26/12
 * Time: 10:56 AM
 * Generates
 */

// TODO: this transformation should be applied based on a flag

public class AddK2SMTLib  extends CopyOnWriteTransformer {

    public static final KLabelConstant K_TO_SMTLIB = KLabelConstant.ofStatic("K2SMTLib");
    public static final String SMTLIB_ATTR = "smtlib";

    private static final String SMTLIB_VAR_PREFIX = "__var__";

    // constructs the term '_+String_(term1,,term2)
    public static Term appendString(Term term1, Term term2, DefinitionHelper definitionHelper) {
        return KApp.of(definitionHelper, KLabelConstant.STRING_PLUSSTRING_KLABEL, term1, term2);
    }


    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        // declare K2SMTlib2 function
        retNode.addConstant(K_TO_SMTLIB);

        // for each sort, define the SMT representation of the symbolic sort
        // constructors symSort(Int), symSort(String) and symSort(Id)
        // TODO: add generic K2String and generate support for symSort(K)
        for (String sort : node.getAllSorts()) {
            if (AddSymbolicK.allowKSymbolic(sort)) {
                String symCtor = AddSymbolicK.symbolicConstructor(sort);

                Variable var = MetaK.getFreshVar("Int");
                Term symTerm = KApp.of(definitionHelper, KLabelConstant.of(symCtor, definitionHelper), var);
                Term lhs = KApp.of(definitionHelper, K_TO_SMTLIB, symTerm);
                KApp strTerm = KApp.of(definitionHelper, KLabelConstant.of("Int2String", definitionHelper), var);
                Term rhs = appendString(StringBuiltin.of(SMTLIB_VAR_PREFIX), strTerm, definitionHelper);
                Rule rule = new Rule(lhs, rhs, definitionHelper);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);

                var = MetaK.getFreshVar("#String");
                symTerm = KApp.of(definitionHelper, KLabelConstant.of(symCtor, definitionHelper), var);
                lhs = KApp.of(definitionHelper, K_TO_SMTLIB, symTerm);
                rhs = appendString(StringBuiltin.of(SMTLIB_VAR_PREFIX), var, definitionHelper);
                rule = new Rule(lhs, rhs, definitionHelper);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);

                var = MetaK.getFreshVar("Id");
                symTerm = KApp.of(definitionHelper, KLabelConstant.of(symCtor, definitionHelper), var);
                lhs = KApp.of(definitionHelper, K_TO_SMTLIB, symTerm);
                strTerm = KApp.of(definitionHelper, KLabelConstant.of("Id2String", definitionHelper), var);
                rhs = appendString(StringBuiltin.of(SMTLIB_VAR_PREFIX), strTerm, definitionHelper);
                rule = new Rule(lhs, rhs, definitionHelper);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);
            }
        }

        // for each production, define the SMT representation based on the
        // smtlib tag
        // TODO: support subsort production using the injection label
        for (Production prod : SyntaxByTag.get(node, SMTLIB_ATTR, definitionHelper)) {
            String smtLbl = prod.getAttribute(SMTLIB_ATTR);
            // not sure if this is necessary
            if (smtLbl == null)
                smtLbl = "";

            // for empty smtlib tags, use the prefix label instead
            // TODO: ensure the label is a valid SMTLib identifier
            if (smtLbl.equals(""))
                smtLbl = prod.getLabel();

            if (prod.isSubsort())
                continue;

            // ignore syntactic lists for now
            if (prod.isListDecl())
                continue;

            Term term = MetaK.getTerm(prod, definitionHelper);
            Term lhs = KApp.of(definitionHelper, K_TO_SMTLIB, term);

            Term rhs;
            if (prod.isConstant()) {
                rhs = StringBuiltin.of(smtLbl);
            } else {
                TermCons termCons = ((TermCons) term);
                rhs = StringBuiltin.of("(" + smtLbl);
                for (int idx = 0; idx < ((TermCons) term).arity(definitionHelper); ++idx) {
                    Variable var = (Variable) termCons.getSubterm(idx);
                    rhs = appendString(rhs, StringBuiltin.SPACE, definitionHelper);
                    rhs = appendString(rhs, KApp.of(definitionHelper, K_TO_SMTLIB, var), definitionHelper);
                }
                rhs = appendString(rhs, StringBuiltin.of(")"), definitionHelper);
            }

            Rule rule = new Rule(lhs, rhs, definitionHelper);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        return retNode;
    }

    public AddK2SMTLib(DefinitionHelper definitionHelper) {
        super("Add translation from K to Z3 SMTlib v2 string", definitionHelper);
    }
}
