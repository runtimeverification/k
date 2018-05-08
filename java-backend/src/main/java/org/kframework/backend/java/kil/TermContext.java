// Copyright (c) 2013-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.Sets;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.KEMException;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext extends JavaSymbolicObject {

    private final AtomicLong counter;

    private final GlobalContext global;

    private Set<Variable> initialVariables;

    private Term topTerm;

    private ConjunctiveFormula topConstraint;

    private KOREtoBackendKIL converter;

    private TermContext(GlobalContext global, AtomicLong counter) {
        this.global = global;
        this.counter = counter;
        this.initialVariables = Sets.newHashSet();
    }

    public Set<Variable> getInitialVariables() {
        return initialVariables;
    }

    public void setInitialVariables(Set<Variable> initialVariables) {
        if (initialVariables == null) {
            Sets.newHashSet();
        } else {
            this.initialVariables = initialVariables;
        }
    }


    /**
     * Forks an identical {@link TermContext}.
     */
    public TermContext fork() {
        return counter != null ? new TermContext(global, new AtomicLong(counter.get())) : this;
    }

    public BigInteger freshConstant() {
        if (counter == null) {
            throw KEMException.criticalError("No fresh counter available in this TermContext.");
        }
        return BigInteger.valueOf(counter.incrementAndGet());
    }

    public long getCounterValue() {
        return counter.get();
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

    public KOREtoBackendKIL getKOREtoBackendKILConverter() {return this.converter;}

    public void setKOREtoBackendKILConverter(KOREtoBackendKIL converter) { this.converter = converter; }

    public ConjunctiveFormula getTopConstraint() {
        return topConstraint;
    }

    public void setTopConstraint(ConjunctiveFormula topConstraint) {
        this.topConstraint = topConstraint;
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
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

        private AtomicLong counter;

        public Builder(GlobalContext globalContext) {
            this.globalContext = globalContext;
        }

        public Builder freshCounter(long initialValue) {
            this.counter = new AtomicLong(initialValue);
            return this;
        }

        public TermContext build() {
            return new TermContext(globalContext, counter);
        }

    }

}
