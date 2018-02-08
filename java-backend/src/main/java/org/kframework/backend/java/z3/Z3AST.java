package org.kframework.backend.java.z3;

import com.sun.jna.Pointer;

public class Z3AST {
    final Pointer ast;
    private final Z3Context context;

    Z3AST(Pointer ast, Z3Context context) {
        this.ast = ast;
        this.context = context;
        LibZ3.INSTANCE.Z3_inc_ref(context.context, ast);
        context.checkError();
    }

    @Override
    protected void finalize() {
        synchronized(context) {
            if (!context.closed) {
                LibZ3.INSTANCE.Z3_dec_ref(context.context, ast);
            }
        }
    }
}
