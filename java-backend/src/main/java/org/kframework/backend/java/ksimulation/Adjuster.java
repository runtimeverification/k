// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.Z3Term;
import org.kframework.backend.java.symbolic.KILtoZ3;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.SymbolicConstraint.Equality;
import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Cell;
import org.kframework.krun.KRunExecutionException;
import org.kframework.utils.options.SMTSolver;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

public class Adjuster {

    private SymbolicRewriter impl;
    private SymbolicRewriter spec;

    public Adjuster(SymbolicRewriter impl,SymbolicRewriter spec){

        this.impl=impl;

        this.spec=spec;
    }

    public boolean isSat(ConstrainedTerm implElem,ConstrainedTerm specElem) throws KRunExecutionException, Z3Exception{

        if(impl.getSimulationMap().isEmpty()
                || spec.getSimulationMap().isEmpty()){

            return true;
        }

        ConstrainedTerm implside = impl.computeSimulationStep(implElem);
        ConstrainedTerm specside = spec.computeSimulationStep(specElem);

        if(specside == null){

            return true;
        }

        if(implside==null){
            return false;
        }

        if(implElem.termContext().definition().context().smtOptions.smt == SMTSolver.NONE){

            return implside.term().equals(specside.term());
        }

        Map<Variable,Variable> implVars =
                implside.constraint().rename(implside.term().variableSet());
        Map<Variable,Variable> specVars =
                specside.constraint().rename(specside.term().variableSet());

        org.kframework.backend.java.kil.Term newImplTerm =
                implside.term().substituteWithBinders(implVars, implside.termContext());

        @SuppressWarnings("unchecked")
        Term newImplContent = ((Cell<Term>)newImplTerm).getContent();

        org.kframework.backend.java.kil.Term newSpecTerm =
                specside.term().substituteWithBinders(specVars, specside.termContext());

        @SuppressWarnings("unchecked")
        Term newSepcContent = ((Cell<Term>)newSpecTerm).getContent();

        SymbolicConstraint newImplside =
                implside.constraint().substituteWithBinders(implVars, implside.termContext());
        SymbolicConstraint newSpecside =
                specside.constraint().substituteWithBinders(specVars, specside.termContext());



        Set<Variable> allVarsInTerm = new HashSet<Variable>();

        allVarsInTerm.addAll(implVars.values());
        allVarsInTerm.addAll(specVars.values());

        Set<Variable> allVars = new HashSet<Variable>();
        allVars.addAll(newImplside.variableSet());
        allVars.addAll(newSpecside.variableSet());
        allVars.addAll(implVars.values());
        allVars.addAll(specVars.values());


        com.microsoft.z3.Context context = new com.microsoft.z3.Context();
        KILtoZ3 transformer = new KILtoZ3(allVars, context);

        Solver solver = context.mkSolver();

        BoolExpr first = context.mkEq(((Z3Term)newImplContent.accept(transformer)).expression(),
                ((Z3Term)newSepcContent.accept(transformer)).expression());

        if(allVarsInTerm.isEmpty()){

            solver.add(first);

            if(solver.check() == Status.SATISFIABLE){
                return true;
                } else if(solver.check()==Status.UNKNOWN){
                    return implside.term().equals(specside.term());
                }

                return false;
        }

        ArrayList<BoolExpr> temp = new ArrayList<BoolExpr>();

        temp.add(first);

        for(Equality equality : newImplside.equalities()){

            BoolExpr tempBoolExpr = context.mkEq(((Z3Term) equality.leftHandSide().accept(transformer)).expression(),
                    ((Z3Term) equality.rightHandSide().accept(transformer)).expression());
            temp.add(tempBoolExpr);
        }

        BoolExpr []  newImplEqualities = new BoolExpr [temp.size()];

        for(int i=0;i<temp.size();++i){

            newImplEqualities[i] = temp.get(i);
        }


        temp = new ArrayList<BoolExpr>();

        for(Equality equality : newSpecside.equalities()){

            BoolExpr tempBoolExpr = context.mkEq(((Z3Term) equality.leftHandSide().accept(transformer)).expression(),
                    ((Z3Term) equality.rightHandSide().accept(transformer)).expression());
            temp.add(tempBoolExpr);
        }

        BoolExpr []  newSpecEqualities = new BoolExpr [temp.size()];

        for(int i=0;i<temp.size();++i){

            newSpecEqualities[i] = temp.get(i);
        }

        BoolExpr forAllLeftSide = context.mkAnd(newImplEqualities);
        BoolExpr forAllRightSide = context.mkAnd(newSpecEqualities);

        Expr [] varsInZ3 = new Expr[allVarsInTerm.size()];

        Iterator<Variable> iter = allVarsInTerm.iterator();

        int i = 0;
        while(iter.hasNext()){

            varsInZ3[i] =
                    ((Z3Term)((org.kframework.backend.java.kil.Term)iter.next()).accept(transformer)).expression();
        }

        solver.add(context.mkForall(varsInZ3,context.mkImplies(forAllLeftSide, forAllRightSide)
                    , 1, null, null, null, null));

        if(solver.check() == Status.SATISFIABLE){
        return true;
        } else if(solver.check()==Status.UNKNOWN){
            return implside.term().equals(specside.term());
        }

        return false;
    }

}
