package org.kframework.backend.java.z3;

import com.sun.jna.Pointer;

public class Z3Solver {
    final Pointer solver;
    private final Z3Context context;

    public Z3Solver(Z3Context context) {
        this.context = context;
        solver = LibZ3.INSTANCE.Z3_mk_solver(context.context);
        LibZ3.INSTANCE.Z3_solver_inc_ref(context.context, solver);
        context.checkError();
    }

    @Override
    protected void finalize() {
        synchronized(context) {
            if (!context.closed) {
                LibZ3.INSTANCE.Z3_solver_dec_ref(context.context, solver);
            }
        }
    }

    public void setParams(Z3Params params) {
        LibZ3.INSTANCE.Z3_solver_set_params(context.context, solver, params.params);
        context.checkError();
    }

    public void _assert(Z3AST ast) {
        LibZ3.INSTANCE.Z3_solver_assert(context.context, solver, ast.ast);
        context.checkError();
    }

    public Z3Status check() {
        int status = LibZ3.INSTANCE.Z3_solver_check(context.context, solver);
        context.checkError();
        return Z3Status.of(status);
    }
}
