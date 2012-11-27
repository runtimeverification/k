package org.kframework.compile.transformers;

import org.kframework.compile.utils.GetSyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
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

    public static final Constant K_TO_SMTLIB2 = Constant.KLABEL("K2SMTLib2");
    private static final String SMTLIB2_VAR_PREFIX = "__var__";
    public static final String SMTLIB2_ATTR = "smtlib";

    public static Term appendString(Term term1, Term term2) {
        ListOfK list = new ListOfK();
        list.add(term1);
        list.add(term2);
        Term term = new KApp(Constant.KLABEL("'_+String_"), list);
        return term;
    }


    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        // declare K2SMTlib2 function
        retNode.addConstant(K_TO_SMTLIB2);

        // for each sort, define the SMT representation of the symbolic sort
        // constructors symSort(Int) and symSort(Id)
        // TODO: add generic K2String and genrate support for symSort(K)
        for (String sort : node.getAllSorts()) {
            if (AddSymbolicK.allowKSymbolic(sort)) {
                String symCtor = AddSymbolicK.symbolicConstructor(sort);

                Variable var = MetaK.getFreshVar("Int");
                Term symTerm = new KApp(Constant.KLABEL(symCtor), var);
                Term lhs = new KApp(K_TO_SMTLIB2, symTerm);
                KApp strTerm = new KApp(Constant.KLABEL("Int2String"), var);
                Term rhs = appendString(Constant.STRING(SMTLIB2_VAR_PREFIX), strTerm);
                Rule rule = new Rule(lhs, rhs);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);

                var = MetaK.getFreshVar("Id");
                symTerm = new KApp(Constant.KLABEL(symCtor), var);
                lhs = new KApp(K_TO_SMTLIB2, symTerm);
                strTerm = new KApp(Constant.KLABEL("Id2String"), var);
                rhs = appendString(Constant.STRING(SMTLIB2_VAR_PREFIX), strTerm);
                rule = new Rule(lhs, rhs);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);
            }
        }

        // for each production, define the SMT representation based on the
        // smtlib tag
        // TODO: support subsort production using the injection label
        for (Production prod : GetSyntaxByTag.applyVisitor(node, SMTLIB2_ATTR)) {
            String smtLbl = prod.getAttribute(SMTLIB2_ATTR);
            // not sure if this is necessary
            if (smtLbl == null)
                smtLbl = "";

            if (smtLbl.equals(""))
                // prefix label assumed to be valid SMTLib2 identifier
                smtLbl = prod.getLabel();

            if (prod.isSubsort())
                continue;

            // ignore syntactic lists for now
            if (prod.isListDecl())
                continue;

            Term term = MetaK.getTerm(prod);
            Term lhs = new KApp(K_TO_SMTLIB2, term);

            Term rhs;
            if (prod.isConstant()) {
                rhs = Constant.STRING(smtLbl);
            } else {
                TermCons termCons = ((TermCons) term);
                rhs = Constant.STRING("(" + smtLbl);
                for (int idx = 0; idx < ((TermCons) term).arity(); ++idx) {
                    Variable var = (Variable) termCons.getSubterm(idx);
                    rhs = appendString(rhs, Constant.SPACE);
                    rhs = appendString(rhs, new KApp(K_TO_SMTLIB2, var));
                }
                rhs = appendString(rhs, Constant.STRING(")"));
            }

            Rule rule = new Rule(lhs, rhs);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        return retNode;
    }


    public AddK2SMTLib() {
        super("Add translation from K to Z3 SMTlib v2 string");
    }
}
