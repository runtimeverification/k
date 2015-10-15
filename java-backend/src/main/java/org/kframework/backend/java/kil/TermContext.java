// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.KEMException;

import java.io.Serializable;

/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext extends JavaSymbolicObject {

    private final FreshCounter counter;

    private final GlobalContext global;

    // TODO(YilongL): do we want to make it thread-safe?
    private static class FreshCounter implements Serializable {
        private long value;

        private FreshCounter(long value) {
            this.value = value;
        }

        private long incrementAndGet() {
            return ++value;
        }
    }

    private Term topTerm;

    private ConjunctiveFormula topConstraint;

    private TermContext(GlobalContext global, FreshCounter counter, Term topTerm) {
        this.global = global;
        this.counter = counter;
        this.topTerm = topTerm;
    }

    /**
     * Returns a new {@link TermContext} with a fresh counter starting from {@code 0}.
     */
    @Deprecated
    public static TermContext of(GlobalContext global) {
        return new TermContext(global, new FreshCounter(0), null);
    }

    /**
     * Forks an identical {@link TermContext}.
     */
    public TermContext fork() {
        return new TermContext(global, new FreshCounter(counter.value), null);
    }

    public long freshConstant() {
        if (counter == null) {
            throw KEMException.criticalError("No fresh counter available in this TermContext.");
        }
        return counter.incrementAndGet();
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

        private Term topTerm;

        public Builder(GlobalContext globalContext) {
            this.globalContext = globalContext;
        }

        public Builder freshCounter(long initialValue) {
            this.counter = new FreshCounter(initialValue);
            return this;
        }

        public Builder topTerm(Term topTerm) {
            this.topTerm = topTerm;
            return this;
        }

        public TermContext build() {
            return new TermContext(globalContext, counter, topTerm);
        }

    }

}
