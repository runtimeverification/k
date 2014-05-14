// Copyright (c) 2012-2014 K Team. All Rights Reserved.

package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.List;

/**
 * User: andrei.arusoaie
 * Date: 12/2/13
 * Time: 9:12 AM
 * This class enables the path condition verification when using the LTL model-checker
 * and the symbolic backend. An LTL property is given using K of the form:
 *
 *   rule B:Bag |=Ltl eqTo(X:Id, I:Int) => true requires val(B, X) ==Int I [ltl, anywhere]
 *
 * The |=Ltl relation checks if the program state (B:Bag - the configuration) satisfies
 * a specific predicate. When using symbolic values in the configuration the condition cannot
 * be always checked (e.g. val(B, X) ==Int I). So, the next possible state should be detected
 * using the SMT solver. This class transforms the rule above into:
 *
 *   rule <generatedTop> B:Bag <path-condition> Phi:K </path-condition></generatedTop>
 *            |=Ltl eqTo(X:Id, I:Int) => true
 *   requires checkSat(Phi andBool notBool(val(B, X) ==Int I)) =K "unsat" [ltl, anywhere]
 *
 * This rule uses the solver to detect if the current path-condition implies the rule condition.
 * Note that this transformation is applied only to those rules tagged with 'ltl' attribute.
 */
public class ResolveLtlAttributes extends CopyOnWriteTransformer {

    // the 'ltl' attribute used to identify the LTL satisfaction rules
    private static final String LTL = "ltl";

    // the LTL satisfaction relation
    public static final String LTL_SAT = "'_|=Ltl_";

    public ResolveLtlAttributes(Context context) {
        super("Resolve LTL attributes", context);
    }

    @Override
    public ASTNode visit(Rule rule, Void _)  {
        if (rule.getAttributes().containsKey(LTL)) {
            Term body = rule.getBody();
            if (body instanceof Rewrite) {
                // search the LTL state
                SearchLTLState searchLTLState = new SearchLTLState(context);
                searchLTLState.visitNode(rule);

                // The LTL state should ALWAYS be a variable.
                // Otherwise, an error message is thrown.
                Term expectedVariable = searchLTLState.getLtlState();
                // extract the actual instance from the AST
                try {
                    expectedVariable = ((KApp) expectedVariable).getLabel();
                    expectedVariable = ((KInjectedLabel) expectedVariable).getTerm();
                } catch (ClassCastException e) {
                    GlobalSettings.kem.register(new KException(
                            KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            "could not extract the term representing the " +
                                    "LTL state from left hand side of the rule",
                            rule.getFilename(),
                            rule.getLocation()));
                }
                // If expectedVariable is not a Variable, then throw an error message.
                if (!(expectedVariable instanceof Variable)) {
                    GlobalSettings.kem.register(new KException(
                            KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            "the 'ltl' attribute can be used only for rules " +
                                    "having only a variable in the left hand side of "
                                    + LTL_SAT,
                            rule.getFilename(),
                            rule.getLocation()));
                } else {
                    // create a variable representing the path condition
                    Variable phi = Variable.getFreshVar("K");

                    // wrap the LTL state variable and the path condition phi with
                    // <generatedTop> cell
                    String ltlVarStateName = ((Variable) expectedVariable).getName();
                    WrapVariableWithTopCell wrapper = new WrapVariableWithTopCell(context, phi, ltlVarStateName);
                    rule = (Rule) wrapper.visitNode(rule);

                    // check if the path condition implies the rule condition
                    // step 1: filter the rule condition by extracting the terms
                    //         which can be translated into SMTLIB
                    Term requires = rule.getRequires();
                    ConditionTransformer ct = new ConditionTransformer(context);
                    Term smtlibInvalidCondition = (Term) ct.visitNode(requires);
                    List<Term> filtered = ct.getFilteredTerms();
                    filtered.add(BoolBuiltin.TRUE);
                    Term smtlibValidCondition = AddPathCondition.andBool(filtered);
                    Term predicates = AddPathCondition.andBool(ct.getGeneratedPredicates());

                    // step 2: prepare to check the implication using the SMT solver
                    Term implicationTerm = createSMTImplicationTerm(phi, smtlibValidCondition, context);

                    // append the implication, the predicates and the rest of the condition
                    // back into the new rule condition
                    requires = KApp.of(KLabelConstant.ANDBOOL_KLABEL, smtlibInvalidCondition, predicates, implicationTerm);

                    // add the new side condition of the rule and return
                    Rule newRule = rule.shallowCopy();
                    newRule.setRequires(requires);
                    return newRule;
                }
            }
        }

        return super.visit(rule, _);
    }

    /**
     * This function creates and returns a term which is used
     * to check the logical implication of two given terms using
     * an SMT solver. For the implication:
     *     x implies y
     * this function returns:
     *     'checkSat(x and not(y)) == "unsat"
     * @param x a logical term
     * @param y a logical term
     * @param context the K definition context
     * @return
     */
    public static Term createSMTImplicationTerm(Term x, Term y, Context context) {
        Term yNegation = KApp.of(KLabelConstant.NOTBOOL_KLABEL, y);
        Term xAndy = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, x, yNegation);
        KApp unsat = StringBuiltin.kAppOf("unsat");
        KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), xAndy);
        return KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, unsat);
    }
}
