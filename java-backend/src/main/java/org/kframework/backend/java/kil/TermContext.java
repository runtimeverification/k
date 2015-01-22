// Copyright (c) 2013-2015 K Team. All Rights Reserved.
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

    private final GlobalContext global;

    private Term topTerm;

    private TermContext(GlobalContext global) {
        this.global = global;
    }

    public static TermContext of(GlobalContext global) {
        return new TermContext(global);
    }

    public static TermContext of(GlobalContext global, Term topTerm, BigInteger counter) {
        TermContext termContext = new TermContext(global);
        termContext.topTerm = topTerm;
        termContext.counter = counter;
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
        return global.getDefinition();
    }

    public FileSystem fileSystem() {
        return global.fs;
    }

    public GlobalContext global() {
        return global;
    }

    public Term getTopTerm() {
        return topTerm;
    }

    public void setTopTerm(Term topTerm) {
        this.topTerm = topTerm;
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
