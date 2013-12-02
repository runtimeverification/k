package org.kframework.backend.symbolic;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.*;
import java.util.List;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 12/2/13
 * Time: 9:12 AM
 * Rules of the form pi |= p when b annotated with LTL attribute
 * becomes pi /\ phi |= p when phi implies b
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
                Rewrite rewrite = (Rewrite) body;
                Term left = rewrite.getLeft();
                Term right = rewrite.getRight();
                Term requires = node.getRequires();
                Term ensures = node.getEnsures();

                // resolve left: B:Bag is transformed into B:Bag <path-condition> Phi </path-condition>

                // declare path condition cell
                Variable phi = Variable.getFreshVar("K");
                Cell pc = new Cell();
                pc.setLabel(MetaK.Constants.pathCondition);
                pc.setEllipses(Cell.Ellipses.NONE);
                pc.setContents(phi);

                if (left instanceof KApp) {
                    KApp kapp = (KApp) left;
                    KList args = (KList) kapp.getChild();
                    Term bagVar = args.getContents().get(0);
                    Term rest = args.getContents().get(1);
                    if (kapp.getLabel() instanceof KLabelConstant) {
                        KLabelConstant ltlSatLabel = (KLabelConstant) kapp.getLabel();
                        if (ltlSatLabel.getLabel().equals(LTL_SAT)) {
                            Bag bag = new Bag();
                            java.util.List<Term> contents = new ArrayList<Term>();
                            contents.add(bagVar.shallowCopy());
                            contents.add(pc);
                            bag.setContents(contents);

                            String varName = ((Variable) ((KInjectedLabel) ((KApp) bagVar).getLabel()).getTerm()).getName();
                            bagVar = bag;
                            rest = (Term) rest.accept(new AddPCToBagVariable(context, pc, varName));
                            // right = (Term) right.accept(new AddPCToBagVariable(context, pc, varName));
                            if (requires != null) {
                                requires = (Term) requires.accept(new AddPCToBagVariable(context, pc, varName));
                            }
                            if (ensures != null) {
                                ensures = (Term) ensures.accept(new AddPCToBagVariable(context, pc, varName));
                            }

                            // transform the rule condition: pi /\ phi |= p when phi implies b
                            // becomes pi /\ phi |= p when checkSat(phi /\ not b) == unsat

                            // step: filter b
                            ConditionTransformer ct = new ConditionTransformer(context);
                            Term bSmtInvalid = (Term) requires.accept(ct);
                            List<Term> filtered = ct.getFilteredTerms();
                            filtered.add(BoolBuiltin.TRUE);
                            Term bSmtValid = AddPathCondition.andBool(filtered);

                            // step: bPrime /\ checkSat(phi /\ not b)
                            Term check = AddPathCondition.checkSat(KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, phi, KApp.of(KLabelConstant.NOTBOOL_KLABEL, bSmtValid)), context);
                            requires = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, bSmtInvalid, check);

                            // reconstruct the rule
                            left = KApp.of(KLabelConstant.of(ltlSatLabel.getLabel()), bagVar, rest);
                            Rule newRule = new Rule(left, right, context);
                            newRule.setRequires(requires);
                            newRule.setEnsures(ensures);
                            return newRule;
                        }
                    }
                }

            }
        }


        return super.transform(node);    //To change body of overridden methods use File | Settings | File Templates.
    }
}
