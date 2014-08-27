// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kcheck.RLBackend;
import org.kframework.kil.ASTNode;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class AddCircularityRules extends CopyOnWriteTransformer {

    public static final String RRULE_ATTR = "reachability-rule";

    private List<ASTNode> reachabilityRules;

    public AddCircularityRules(Context context, List<ASTNode> reachabilityRules) {
        super("Add circularity rules", context);
        this.reachabilityRules = reachabilityRules;
    }

    @Override
    public ASTNode visit(Module node, Void _)  {

        ArrayList<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
        Module module = node.shallowCopy();
        module.setItems(items);


        for (ASTNode rr : reachabilityRules) {
            if (rr instanceof Sentence) {
                Sentence r = (Sentence) rr;

                // "parse" the reachability rules
                ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(
                        context);
                parser.visitNode(r);

                Term newPi = parser.getPi().shallowCopy();
                Variable K = Variable.getFreshVar(Sort.K);

                // extract the content of the K cell (PGM) from LHS of
                // the reachability rule and replace it by PGM ~> K
                ExtractCellContent extract = new ExtractCellContent(context, "k");
                extract.visitNode(newPi);
                Term pgm = extract.getContent().shallowCopy();

                // push the new program without the first label
                Term pgmprime = pgm.shallowCopy();
                RemoveLabel pl = new RemoveLabel(context);
                pgmprime = (Term) pl.visitNode(pgmprime);

                List<Term> cnt = new ArrayList<Term>();
                cnt.add(pgm);
                cnt.add(pgmprime); // append the pgmprime too
                cnt.add(K);
                KSequence newContent = new KSequence(cnt);

                SetCellContent app = new SetCellContent(context, newContent, "k");
                newPi = (Term) app.visitNode(newPi);

                // in RHS, replace .K with K
                Term newPiPrime = parser.getPi_prime().shallowCopy();
                SetCellContent appPrime = new SetCellContent(context, K, "k");
                newPiPrime = (Term) appPrime.visitNode(newPiPrime);

                // fresh variables
                VariablesVisitor vvleft = new VariablesVisitor(context);
                vvleft.visitNode(parser.getPi());

//                System.out.println("CFG VARS: " + vvleft.getVariables());
//                System.out.println("FROM: " + parser.getPi());
//
                VariablesVisitor vvright = new VariablesVisitor(context);
                vvright.visitNode(parser.getPi_prime());

//                System.out.println("CFG' VARS: " + vvright.getVariables());
//                System.out.println("FROM: " + parser.getPi_prime());
//
                List<Term> fresh = new ArrayList<Term>();

                for(Variable v : vvright.getVariables()){
                    if (!varInList(v, vvleft.getVariables())){
                        List<Term> vlist = new ArrayList<Term>();
                        vlist.add(v);
//                        System.out.println("Generate fresh "  + v);
                        //fresh.add(new TermCons(v.getSort(), MetaK.Constants.freshCons, vlist, context));
//                        fresh.add(KApp.of(KLabelConstant.of(AddSymbolicK.symbolicConstructor(v.getSort())), org.kframework.kil.Token.kAppOf("#Id", v.getName())));
                    }
                }

                // insert patternless formulas into condition
                Term phi = parser.getPhi().shallowCopy();
                Term phiPrime = parser.getPhi_prime().shallowCopy();
                Term rrcond = KApp.of(KLabelConstant.of(RLBackend.INTERNAL_KLABEL, context), phi, phiPrime);
                fresh.add(rrcond);

//                Term condition = KApp.of(KLabelConstant.ANDBOOL_KLABEL, new KList(fresh));
                Term condition = andBool(fresh);

                Rule circRule = new Rule(newPi, newPiPrime, context);
                circRule.setRequires(condition);
                int correspondingIndex = reachabilityRules.indexOf(rr);
                circRule.addAttribute(RRULE_ATTR, correspondingIndex + "");

                items.add(circRule);
            }
        }

        return module;
    }

    private Term andBool(List<Term> terms) {
        if (terms.size() == 0)
            return BoolBuiltin.TRUE;
        Term term = terms.get(0);
        terms.remove(0);
        return KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, term, andBool(terms));
    }

    public static boolean varInList(Variable v, List<Variable> vars) {
        for(Variable var : vars){
            if (v.getName().equals(var.getName())) {
                return true;
            }
        }
        return false;
    }
}
