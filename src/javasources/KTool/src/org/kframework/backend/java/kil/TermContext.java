package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.krun.api.io.FileSystem;


/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext extends JavaSymbolicObject {

    private final Definition def;
    private final FileSystem fs;

    public TermContext(Definition def, FileSystem fs) {
        this.def = def;
        this.fs = fs;
    }

    // this constructor should never be used except in cases where the Term is part of a Definition
    // instead of part of a ConstrainedTerm.
    public TermContext(Definition def) {
        this.def = def;
        this.fs = null;
    }


    public Definition definition() {
        return def;
    }

    public FileSystem fileSystem() {
        return fs;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

}
