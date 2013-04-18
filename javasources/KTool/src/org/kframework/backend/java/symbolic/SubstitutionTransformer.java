package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.kil.KCollectionFragment;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.util.HashSet;
import java.util.List;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 9:37 PM
 * To change this template use File | Settings | File Templates.
 */
public class SubstitutionTransformer extends CopyOnWriteTransformer {

    private final java.util.Set<Variable> boundVariables;
    private final java.util.Map<Variable, Term> substitution;

    public SubstitutionTransformer(java.util.Map<Variable, Term> substitution) {
        this.substitution = substitution;
        boundVariables = new HashSet<Variable>();
    }

    @Override
    public KList transform(KList kList) {
        if (kList.hasFrame()) {
            Variable frame = kList.getFrame();
            kList = (KList) super.transform(new KList(kList.getItems()));
            return new KList(kList.getItems(), frame);
        } else {
            return (KList) super.transform(kList);
        }
    }

    @Override
    public KSequence transform(KSequence kSequence) {
        if (!kSequence.hasFrame() || boundVariables.contains(kSequence.getFrame())) {
            return (KSequence) super.transform(kSequence);
        }

        Term term = substitution.get(kSequence.getFrame());
        if (term == null || !(term instanceof KCollectionFragment)) {
            return (KSequence) super.transform(kSequence);
        }

        KCollectionFragment fragment = (KCollectionFragment) term;
        List<Term> items = transformList(kSequence.getItems());
        ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
        builder.addAll(items).addAll(fragment);

        if (fragment.hasFrame()) {
            kSequence = new KSequence(builder.build(), fragment.getFrame());
        } else {
            kSequence = new KSequence(builder.build());
        }

        return kSequence;
    }

    @Override
    public Map transform(Map map) {
        if (!map.hasFrame() || boundVariables.contains(map.getFrame())) {
            return (Map) super.transform(map);
        }

        Term term = substitution.get(map.getFrame());
        if (term == null || term instanceof Variable) {
            return (Map) super.transform(map);
        }



        throw new RuntimeException();
    }

    @Override
    public Term transform(Variable variable) {
        if (boundVariables.contains(variable)) {
            return variable;
        }

        Term term = substitution.get(variable);
        if (term != null) {
            if (term instanceof KCollectionFragment) {
                KCollectionFragment fragment = (KCollectionFragment) term;
                ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
                builder.addAll(fragment);

                KSequence kSequence;
                if (fragment.hasFrame()) {
                    kSequence = new KSequence(builder.build(), fragment.getFrame());
                } else {
                    kSequence = new KSequence(builder.build());
                }

                return kSequence;
            } else {
                return term;
            }
        } else {
            return variable;
        }
    }

}
