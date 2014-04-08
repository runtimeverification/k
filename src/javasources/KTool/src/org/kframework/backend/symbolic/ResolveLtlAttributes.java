// Copyright (C) 2012-2014 K Team. All Rights Reserved.

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
import org.kframework.kil.visitors.exceptions.TransformerException;
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
    public ASTNode transform(Rule rule) throws TransformerException {
        if (rule.getAttributes().containsKey(LTL)) {
            Term body = rule.getBody();
            if (body instanceof Rewrite) {
                // get the rule's side condition
                Term requires = rule.getRequires();

                // search the LTL state
                SearchLTLState searchLTLState = new SearchLTLState(context);
                rule.accept(searchLTLState);

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
                    rule = (Rule) rule.accept(wrapper);

                    // check if the path condition implies the rule condition
                    // step 1: filter the condition and separate the smtValid part
                    //         of it (operations which can be sent to the
                    //         SMT solver) from the smtInvalid clauses.
                    //         For the latter add predicates in condition.
                    ConditionTransformer ct = new ConditionTransformer(context);
                    Term smtInvalidCondition = (Term) requires.accept(ct);
                    List<Term> filtered = ct.getFilteredTerms();
                    filtered.add(BoolBuiltin.TRUE);
                    Term smtValidCondition = AddPathCondition.andBool(filtered);
                    Term predicates = AddPathCondition.andBool(ct.getGeneratedPredicates());

                    // step 2: check the implication using the SMT solver using 'checkSat;
                    // Note that we use smtValid instead of the rule condition because
                    // predicates are not important when checking the implication.
                    Term conditionNegation = KApp.of(KLabelConstant.NOTBOOL_KLABEL, smtValidCondition);
                    Term implication = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, phi, conditionNegation);
                    KApp unsat = StringBuiltin.kAppOf("unsat");
                    KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), implication);
                    Term equalsUnsat = KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, unsat);
                    // append the implication and the predicates to condition
                    requires = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, smtInvalidCondition, equalsUnsat);
                    requires = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, predicates, requires);

                    // add the new side condition of the rule and return
                    Rule newRule = rule.shallowCopy();
                    newRule.setRequires(requires);
                    return newRule;
                }
            }
        }

        return super.transform(rule);
    }
}
