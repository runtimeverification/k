// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.SMTSolver;

import java.io.Serializable;

import com.google.inject.Inject;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;


public class UseSMT implements Serializable {

    private final SMTOptions options;

    @Inject
    public UseSMT(SMTOptions options) {
        this.options = options;
    }

    public Term checkSat(Term term, TermContext termContext) {
        if (options.smt != SMTSolver.Z3) {
            return null;
        }

        BuiltinMap.Builder resultBuilder = BuiltinMap.builder(termContext.global());
        try {
            ConjunctiveFormula constraint = ConjunctiveFormula.of(termContext.global())
                    .add(term, BoolToken.TRUE);
            com.microsoft.z3.Context context = new com.microsoft.z3.Context();
            Solver solver = context.mkSolver();
            BoolExpr query = context.parseSMTLIB2String(
                    // TODO(AndreiS): this should be included from the default smt prelude
                    "(declare-sort IntSeq)" + KILtoSMTLib.translateConstraint(constraint),
                    null,
                    null,
                    null,
                    null);
            solver.add(query);


            if(solver.check() == Status.SATISFIABLE){

                Model model = solver.getModel();
                FuncDecl[] consts = model.getConstDecls();

                for(int i=0 ; i < consts.length; ++i){

                    Expr resultFrg = model.getConstInterp(consts[i]);

                    Variable akey = new Variable(consts[i].getName().toString(), Sort.of(consts[i].getRange().toString()));

                    IntToken avalue = IntToken.of(Integer.parseInt(resultFrg.toString()));

                    resultBuilder.put(akey, avalue);
                }


            }
            context.dispose();
        } catch (Z3Exception e) {
            e.printStackTrace();
        } catch (UnsupportedOperationException e) {
            // TODO(AndreiS): fix this translation and the exceptions
            e.printStackTrace();
        }
        return resultBuilder.build();
    }
}
