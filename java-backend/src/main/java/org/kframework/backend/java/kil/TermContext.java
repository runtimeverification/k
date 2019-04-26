// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.Sets;
import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.KEMException;

import javax.annotation.Nonnull;
import java.math.BigInteger;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;

/**
 * An object containing context specific to a particular configuration.
 */
public class TermContext {

    private final AtomicLong counter;

    private final GlobalContext global;

    private Set<Variable> initialLhsVariables;

    private Term topTerm;

    private ConjunctiveFormula topConstraint;

    private KOREtoBackendKIL converter;

    public final AtomicInteger exceptionLogCount = new AtomicInteger();

    private TermContext(GlobalContext global, AtomicLong counter) {
        this.global = global;
        this.counter = counter;
        this.initialLhsVariables = Sets.newHashSet();
    }

    public Set<Variable> getInitialLhsVariables() {
        return initialLhsVariables;
    }

    public void setInitialLhsVariables(@Nonnull Set<Variable> initialLhsVariables) {
        this.initialLhsVariables = initialLhsVariables;
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
