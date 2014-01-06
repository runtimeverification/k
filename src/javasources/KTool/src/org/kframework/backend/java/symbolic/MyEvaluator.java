package org.kframework.backend.java.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;


/**
 * Evaluates functions/predicates and collects symbolic constraint generated
 * in the evaluation process.
 * 
 * @author YilongL
 */
public class MyEvaluator extends PrePostTransformer {

//    private final List<UninterpretedConstraint> multiConstraints = new ArrayList<UninterpretedConstraint>();
    
    private final SymbolicConstraint constraint;

    private MyEvaluator(SymbolicConstraint constraint, TermContext context) {
        super(context);
        this.constraint = constraint;
        this.getPostTransformer().addTransformer(new LocalEvaluator(constraint, context));
//        this.getPostTransformer().addTransformer(new LocalConstraintCollector(multiConstraints));
    }
    
    public SymbolicConstraint constraint() {
        return constraint;
    }
    
    public static Term evaluate(Term term, SymbolicConstraint constraint,
            TermContext context) {
        MyEvaluator evaluator = new MyEvaluator(constraint, context);
        return (Term) term.accept(evaluator);
    }
    
//    /**
//     * TODO(YilongL)
//     * @param term
//     * @param context
//     * @return
//     */
//    public static Pair<Term, List<UninterpretedConstraint>> evaluate(Term term, TermContext context) {
//        MyEvaluator evaluator = new MyEvaluator(context);
//        Term newTerm = (Term) term.accept(evaluator);
//        
//        Pair<Term, List<UninterpretedConstraint>> result = new ImmutablePair<Term, List<UninterpretedConstraint>>(
//                newTerm, evaluator.multiConstraints);
//        return result;
//    }
}
