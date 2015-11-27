// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.KEMException;

import java.io.Serializable;
import java.math.BigInteger;

/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext extends JavaSymbolicObject {

    private final FreshCounter counter;

    private final GlobalContext global;

    /**
     * This class shall not be accessed by more than one thread,
     * so it is made non-thread-safe intentionally.
     */
    private static class FreshCounter implements Serializable {
        private BigInteger value;

        private FreshCounter(BigInteger value) {
            this.value = value;
        }

        private BigInteger incrementAndGet() {
            value = value.add(BigInteger.ONE);
            return value;
        }
    }

    private Term topTerm;

    private ConjunctiveFormula topConstraint;

    private TermContext(GlobalContext global, FreshCounter counter) {
        this.global = global;
        this.counter = counter;
    }

    /**
     * Forks an identical {@link TermContext}.
     */
    public TermContext fork() {
        return counter != null ? new TermContext(global, new FreshCounter(counter.value)) : this;
    }

    public BigInteger freshConstant() {
        if (counter == null) {
            throw KEMException.criticalError("No fresh counter available in this TermContext.");
        }
        return counter.incrementAndGet();
    }

    public BigInteger getCounterValue() {
        return counter.value;
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

    public ConjunctiveFormula getTopConstraint() {
        return topConstraint;
    }

    public void setTopConstraint(ConjunctiveFormula topConstraint) {
        this.topConstraint = topConstraint;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

    public static Builder builder(GlobalContext globalContext) {
        return new Builder(globalContext);
    }

    public static class Builder {

        private final GlobalContext globalContext;

        private FreshCounter counter;

        public Builder(GlobalContext globalContext) {
            this.globalContext = globalContext;
        }

        public Builder freshCounter(long initialValue) {
            return freshCounter(BigInteger.valueOf(initialValue));
        }

        public Builder freshCounter(BigInteger initialValue) {
            this.counter = new FreshCounter(initialValue);
            return this;
        }

        public TermContext build() {
            return new TermContext(globalContext, counter);
        }

    }

}
