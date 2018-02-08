package org.kframework.backend.java.z3;

import com.sun.jna.Callback;
import com.sun.jna.Library;
import com.sun.jna.Native;
import com.sun.jna.Pointer;
import org.kframework.backend.java.util.Z3Wrapper;

interface LibZ3 extends Library {
    LibZ3 INSTANCE = (LibZ3)
            Native.synchronizedLibrary(
                Native.loadLibrary("z3",
                    LibZ3.class));

    interface Z3_error_handler extends Callback {
        void invoke(Pointer context, int errorCode);
    }

    Pointer Z3_mk_config();
    void Z3_del_config(Pointer config);
    Pointer Z3_mk_context_rc(Pointer config);
    void Z3_del_context(Pointer context);
    Pointer Z3_mk_solver(Pointer context);
    void Z3_solver_inc_ref(Pointer context, Pointer solver);
    void Z3_solver_dec_ref(Pointer context, Pointer solver);
    Pointer Z3_mk_params(Pointer context);
    void Z3_params_inc_ref(Pointer context, Pointer params);
    void Z3_params_dec_ref(Pointer context, Pointer params);
    void Z3_params_set_uint(Pointer context, Pointer params, Pointer symbol, int v);
    Pointer Z3_mk_string_symbol(Pointer context, String s);
    void Z3_solver_set_params(Pointer context, Pointer solver, Pointer params);
    Pointer Z3_parse_smtlib2_string(Pointer context, String str, int num_sorts, Pointer sort_names, Pointer sorts, int num_decls, Pointer decl_names, Pointer decls);
    void Z3_inc_ref(Pointer context, Pointer ast);
    void Z3_dec_ref(Pointer context, Pointer ast);
    void Z3_solver_assert(Pointer context, Pointer solver, Pointer ast);
    int Z3_solver_check(Pointer context, Pointer solver);

    void Z3_set_error_handler(Pointer context, Z3_error_handler handler);
    String Z3_get_error_msg(Pointer context, int errno);
}
