package org.kframework.backend.java.z3;

import com.sun.jna.Pointer;

public class Z3Params {
    final Pointer params;
    private final Z3Context context;

    public Z3Params(Z3Context context) {
        this.context = context;
        params = LibZ3.INSTANCE.Z3_mk_params(context.context);
        LibZ3.INSTANCE.Z3_params_inc_ref(context.context, params);
        context.checkError();
    }

    @Override
    protected void finalize() {
        synchronized(context) {
            if (!context.closed) {
                LibZ3.INSTANCE.Z3_solver_dec_ref(context.context, params);
            }
        }
    }

    public void add(String name, int value) {
        Pointer symbol = LibZ3.INSTANCE.Z3_mk_string_symbol(context.context, name);
        LibZ3.INSTANCE.Z3_params_set_uint(context.context, params, symbol, value);
        context.checkError();
    }
}
