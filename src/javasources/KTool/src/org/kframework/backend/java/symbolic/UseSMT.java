package org.kframework.backend.java.symbolic;

import java.io.Serializable;

import org.kframework.backend.java.kil.BuiltinMap;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.kil.Z3Term;

import java.util.*;

import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;

import org.kframework.kil.Context;
import org.kframework.krun.K;



public class UseSMT implements Serializable {

    public static BuiltinMap checkSat(Term term, TermContext termContext) {
        if (!K.smt.equals("z3")) {
            return null;
        }

        BuiltinMap result = new BuiltinMap();   
        try {
            com.microsoft.z3.Context context = new com.microsoft.z3.Context();
            KILtoZ3 transformer = new KILtoZ3(Collections.<Variable>emptySet(), context);
            Solver solver = context.MkSolver();
            
            BoolExpr query = (BoolExpr) ((Z3Term) term.accept(transformer)).expression(); 
            solver.Assert(query);
            
            
            if(solver.Check() == Status.SATISFIABLE){
            	
            	Map<Term,Term> entries = new HashMap<Term,Term>();
            	
            	Model model = solver.Model();
            	FuncDecl[] consts = model.ConstDecls();
            	
            	for(int i=0 ; i < consts.length; ++i){
            		
            		Expr resultFrg = model.ConstInterp(consts[i]);
            		            		
            		Variable akey = new Variable(consts[i].Name().toString(), consts[i].Range().toString());
            		
            		IntToken avalue = IntToken.of(Integer.parseInt(resultFrg.toString()));
            		
            		result.put((Term)akey,(Term)avalue);
            	}
            	
            	
            }
            context.Dispose();
        } catch (Z3Exception e) {
            e.printStackTrace();
        } catch (RuntimeException e) {
            // TODO(AndreiS): fix this translation and the exceptions
            e.printStackTrace();
        }
        return result;
    }
}
