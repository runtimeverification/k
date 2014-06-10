// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.math.BigInteger;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.krun.api.io.FileSystem;

/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext extends JavaSymbolicObject {

    private BigInteger counter = BigInteger.ZERO;
    private final Definition def;
    private final FileSystem fs;

    private TermContext(Definition def, FileSystem fs) {
        this.def = def;
        this.fs = fs;
    }

    /**
     * Only used when the Term is part of a Definition instead of part of a
     * ConstrainedTerm.
     */
    public static TermContext of(Definition def) {
        return new TermContext(def, null);
    }

    public static TermContext of(Definition def, FileSystem fs) {
        return new TermContext(def, fs);
    }

    public BigInteger getCounter() {
        return counter;
    }

    public void setCounter(BigInteger counter) {
        this.counter = counter;
    }

    public BigInteger incrementCounter() {
        counter = this.counter.add(BigInteger.ONE);
        return counter;
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
