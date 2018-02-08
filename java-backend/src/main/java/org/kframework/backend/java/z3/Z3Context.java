package org.kframework.backend.java.z3;

import com.sun.jna.Pointer;

import java.util.Optional;
import java.util.OptionalInt;

public class Z3Context implements AutoCloseable {
    final Pointer config;
    final Pointer context;

    volatile boolean closed = false;

    private OptionalInt errno = OptionalInt.empty();

    public Z3Context() {
        config = LibZ3.INSTANCE.Z3_mk_config();
        context = LibZ3.INSTANCE.Z3_mk_context_rc(config);
        LibZ3.INSTANCE.Z3_set_error_handler(context, (ctx, errno) -> {
            this.errno = OptionalInt.of(errno);
        });
        checkError();
    }

    @Override
    protected void finalize() {
        close();
    }

    public Z3AST parseSmtlib2(String query) {
        Pointer ast = LibZ3.INSTANCE.Z3_parse_smtlib2_string(context, query, 0, Pointer.NULL, Pointer.NULL, 0, Pointer.NULL, Pointer.NULL);
        checkError();
        return new Z3AST(ast, this);
    }

    @Override
    public synchronized void close() {
        if (!closed) {
            closed = true;
            LibZ3.INSTANCE.Z3_del_context(context);
            LibZ3.INSTANCE.Z3_del_config(config);
        }
    }

    void checkError() {
        if (errno.isPresent()) {
            int err = errno.getAsInt();
            errno = OptionalInt.empty();
            throw new Z3Exception(LibZ3.INSTANCE.Z3_get_error_msg(context, err));
        }
    }
}
