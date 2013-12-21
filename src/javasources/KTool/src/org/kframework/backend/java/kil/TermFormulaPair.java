package org.kframework.backend.java.kil;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.kframework.backend.java.symbolic.MyEvaluator;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.UninterpretedConstraint;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import com.google.common.collect.ImmutableList;

/**
 * A pair consisting a {@code Term} and an associated
 * {@code UninterpretedConstraint}.
 * <p>
 * This class can be used to represent the return value of function/predicate
 * evaluation which results in a {@code Term} and possibly an associated formula
 * in the form of {@code UninterpretedConstraint}.
 * <p>
 * This class serves as merely a container for holding intermediate result
 * during evaluation, and, consequently, shall not appear inside the return
 * value of {@link MyEvaluator#evaluate(Term, TermContext)}.
 * 
 * @author YilongL
 * 
 */
@SuppressWarnings("serial")
public class TermFormulaPair extends Term {
    
    private final Term term;
    private final List<UninterpretedConstraint> multiConstraints;

    public TermFormulaPair(Term term,
            List<UninterpretedConstraint> multiConstraints) {
        super(term.kind);
        assert !term.getClass().equals(TermFormulaPair.class) : 
            "The K term wrapped inside this TermFormulaPair should be real K term.";

        this.term = term;
        ImmutableList.Builder<UninterpretedConstraint> builder = ImmutableList.builder();
        builder.addAll(multiConstraints);
        this.multiConstraints = builder.build();
    }
    
    public TermFormulaPair(Term term, UninterpretedConstraint uninterpretedConstraint) {
        this(term, Collections.singletonList(uninterpretedConstraint));
    }
    
    public Term term() {
        return term;
    }
    
    public List<UninterpretedConstraint> multiConstraints() {
        return multiConstraints;
    }
    
    @Override
    public Term evaluate(TermContext context) {
        throw new UnsupportedOperationException();
    }
    
    @Override
    public Term substitute(Map<Variable, ? extends Term> substitution, TermContext context) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term substituteWithBinders(Map<Variable, ? extends Term> substitution, TermContext context) {
        throw new UnsupportedOperationException();
    }

    public Term substituteAndEvaluate(Map<Variable, ? extends Term> substitution, TermContext context) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term substituteWithBinders(Variable variable, Term term, TermContext context) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return this.accept(transformer);
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean isSymbolic() {
        throw new UnsupportedOperationException();
    }

}
