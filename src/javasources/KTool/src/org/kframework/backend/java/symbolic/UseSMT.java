// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.utils.options.SMTSolver;

import java.io.Serializable;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;


public class UseSMT implements Serializable {

    public static Term checkSat(Term term, TermContext termContext) {
        if (termContext.definition().context().smtOptions.smt != SMTSolver.Z3) {
            return null;
        }

        BuiltinMap.Builder resultBuilder = BuiltinMap.builder();
        try {
            com.microsoft.z3.Context context = new com.microsoft.z3.Context();
            Solver solver = context.MkSolver();

            BoolExpr query = KILtoSMTLib.kilToZ3(context, term);
            solver.Assert(query);


            if(solver.Check() == Status.SATISFIABLE){

                Model model = solver.Model();
                FuncDecl[] consts = model.ConstDecls();

                for(int i=0 ; i < consts.length; ++i){

                    Expr resultFrg = model.ConstInterp(consts[i]);

                    Variable akey = new Variable(consts[i].Name().toString(), Sort.of(consts[i].Range().toString()));

                    IntToken avalue = IntToken.of(Integer.parseInt(resultFrg.toString()));

                    resultBuilder.put(akey, avalue);
                }


            }
            context.Dispose();
        } catch (Z3Exception e) {
            e.printStackTrace();
        } catch (UnsupportedOperationException e) {
            // TODO(AndreiS): fix this translation and the exceptions
            e.printStackTrace();
        }
        return resultBuilder.build();
    }
}
