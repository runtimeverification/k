package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
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

    private static final String LTL = "ltl";
    private static final String LTL_SAT = "'_|=Ltl_";

    public ResolveLtlAttributes(Context context) {
        super("Resolve LTL attributes", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {

        if (node.getAttributes().containsKey(LTL)) {
            Term body = node.getBody();
            if (body instanceof Rewrite) {

                // split the rule content into components
                Rewrite rewrite = (Rewrite) body;
                Term rewriteLHS = rewrite.getLeft();
                Term rewriteRHS = rewrite.getRight();
                Term requires = node.getRequires();
                Term ensures = node.getEnsures();


                // process the left hand side
                if (rewriteLHS instanceof KApp) {
                    // extract the left hand side top KApp
                    KApp rewriteLHSBody = (KApp) rewriteLHS;
                    if (rewriteLHSBody.getLabel() instanceof KLabelConstant) {
                        // get left hand side KLabel
                        KLabelConstant rewriteLHSLabel = (KLabelConstant) rewriteLHSBody.getLabel();

                        // check if the left hand side KLabel is '|=Ltl
                        if (rewriteLHSLabel.getLabel().equals(LTL_SAT)) {
                            // Prepare to extract the components of the '|=Ltl KApp body which
                            // should ALWAYS have a variable representing the program state in the
                            // left hand side and a predicate in the right hand side:
                            //     B |=Ltl predicate
                            KList rewriteLHSContents = (KList) rewriteLHSBody.getChild();

                            Term expectedVariable = rewriteLHSContents.getContents().get(0);
                            // extract the actual Variable instance from the AST
                            expectedVariable = ((KApp) expectedVariable).getLabel();
                            expectedVariable = ((KInjectedLabel) expectedVariable).getTerm();

                            // If expectedVariable is not a Variable, then throw an error message.
                            if (!(expectedVariable instanceof Variable)) {
                                GlobalSettings.kem.register(new KException(
                                        KException.ExceptionType.ERROR,
                                        KException.KExceptionGroup.CRITICAL,
                                        "the 'ltl' attribute can be used only for rules " +
                                                "having only a variable in the left hand side of "
                                                + LTL_SAT,
                                        node.getFilename(),
                                        node.getLocation()));
                            } else {
                                // process the variable: wrap it with generatedTop and add the path condition
                                Variable phi = Variable.getFreshVar("K");
                                Term ltlState = WrapVariableWithTopCell.wrapPCAndVarWithGeneratedTop(phi, expectedVariable);

                                // process the predicate: traverse it and replace all the
                                // occurrences of expectedVariable with the newly constructed ltlState
                                String ltlVarStateName = ((Variable) expectedVariable).getName();
                                Term ltlPredicate = rewriteLHSContents.getContents().get(1);
                                ltlPredicate = (Term) ltlPredicate.accept(new WrapVariableWithTopCell(context, phi, ltlVarStateName));

                                // process the right hand side of the rule
                                rewriteRHS = (Term) rewriteRHS.accept(new WrapVariableWithTopCell(context, phi, ltlVarStateName));

                                // process the rule's conditions
                                if (requires != null) {
                                    requires = (Term) requires.accept(new WrapVariableWithTopCell(context, phi, ltlVarStateName));
                                }
                                if (ensures != null) {
                                    ensures = (Term) ensures.accept(new WrapVariableWithTopCell(context, phi, ltlVarStateName));
                                }

                                // transform the rule:  pi /\ phi |= p when phi implies b
                                // into pi /\ phi |= p when checkSat(phi /\ not b) == unsat
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

                                // step 2: check the implication using the SMT solver:
                                //         phi implies b is equivalent with checkSat(phi /\ not b).
                                // Note that we use smtValid instead of b because predicates are not
                                // important when checking the implication.
                                Term conditionNegation = KApp.of(KLabelConstant.NOTBOOL_KLABEL, smtValidCondition);
                                Term implication = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, phi, conditionNegation);
                                KApp unsat = StringBuiltin.kAppOf("unsat");
                                KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), implication);
                                Term equalsUnsat = KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, unsat);
                                // append the implication and the predicates to condition
                                requires = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, smtInvalidCondition, equalsUnsat);
                                requires = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, predicates, requires);

                                // reconstruct the rule and return
                                ltlState = KApp.of(new KInjectedLabel(ltlState), KList.EMPTY);
                                rewriteLHS = KApp.of(KLabelConstant.of(rewriteLHSLabel.getLabel()), ltlState, ltlPredicate);
                                Rule newRule = new Rule(rewriteLHS, rewriteRHS, context);
                                newRule.setRequires(requires);
                                newRule.setEnsures(ensures);
                                return newRule;
                            }
                        }
                    }
                }

            }
        }

        return super.transform(node);
    }
}
