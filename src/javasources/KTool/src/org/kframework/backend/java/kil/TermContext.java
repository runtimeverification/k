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

    public final GlobalContext global;

    private ConstrainedTerm.Data topConstrainedTermData;

    private TermContext(GlobalContext global) {
        this.global = global;
    }

    public static TermContext of(GlobalContext global) {
        return new TermContext(global);
    }

    public static TermContext of(GlobalContext global, ConstrainedTerm.Data topConstrainedTermData) {
        TermContext termContext = new TermContext(global);
        termContext.setConstrainedTermData(topConstrainedTermData);
        return termContext;
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
        return global.def;
    }

    public FileSystem fileSystem() {
        return global.fs;
    }

    public ConstrainedTerm.Data getConstrainedTermData() {
        return topConstrainedTermData;
    }

    public void setConstrainedTermData(ConstrainedTerm.Data constrainedTermData) {
        this.topConstrainedTermData = constrainedTermData;
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
