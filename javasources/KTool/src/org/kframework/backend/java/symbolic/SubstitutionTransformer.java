package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.ImmutableList;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 9:37 PM
 * To change this template use File | Settings | File Templates.
 */
public class SubstitutionTransformer extends CopyOnWriteTransformer {

    private final Set<Variable> boundVariables;
    private final Map<Variable, ? extends Term> substitution;

    public SubstitutionTransformer(Map<Variable, ? extends Term> substitution, Definition definition) {
    	super(definition);
        this.substitution = substitution;
        boundVariables = new HashSet<Variable>();
    }

    @Override
    public KList transform(KList kList) {
        if (kList.hasFrame()) {
            Variable frame = kList.frame();
            kList = (KList) super.transform(new KList(kList.getItems()));
            return new KList(kList.getItems(), frame);
        } else {
            return (KList) super.transform(kList);
        }
    }

    @Override
    public KSequence transform(KSequence kSequence) {
        if (!kSequence.hasFrame() || boundVariables.contains(kSequence.frame())) {
            return (KSequence) super.transform(kSequence);
        }

        Term term = substitution.get(kSequence.frame());
        if (term == null || !(term instanceof KCollectionFragment)) {
            return (KSequence) super.transform(kSequence);
        }

        KCollectionFragment fragment = (KCollectionFragment) term;
        List<Term> items = transformList(kSequence.getItems());
        ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
        builder.addAll(items).addAll(fragment);

        if (fragment.hasFrame()) {
            kSequence = new KSequence(builder.build(), fragment.frame());
        } else {
            kSequence = new KSequence(builder.build());
        }

        return kSequence;
    }

    @Override
    public BuiltinMap transform(BuiltinMap builtinMap) {
        if (!builtinMap.hasFrame() || boundVariables.contains(builtinMap.frame())) {
            return (BuiltinMap) super.transform(builtinMap);
        }

        Term term = substitution.get(builtinMap.frame());
        if (term == null || term instanceof Variable) {
            return (BuiltinMap) super.transform(builtinMap);
        }

        if (term instanceof BuiltinMap) {
            boundVariables.add(builtinMap.frame());
            HashMap<Term, Term> entries = new HashMap<Term, Term>(
                    ((BuiltinMap) super.transform(builtinMap)).getEntries());
            entries.putAll(((BuiltinMap) term).getEntries());
            BuiltinMap returnMap = ((BuiltinMap) term).hasFrame() ?
                    new BuiltinMap(entries, ((BuiltinMap) term).frame()) : new BuiltinMap(entries);
            boundVariables.remove(builtinMap.frame());
            return returnMap;
        }

        throw new RuntimeException();
    }

     @Override
    public BuiltinSet transform(BuiltinSet builtinSet) {
        if (!builtinSet.hasFrame() || boundVariables.contains(builtinSet.frame())) {
            return (BuiltinSet) super.transform(builtinSet);
        }

        Term term = substitution.get(builtinSet.frame());
        if (term == null || term instanceof Variable) {
            return (BuiltinSet) super.transform(builtinSet);
        }

        if (term instanceof BuiltinSet) {
            boundVariables.add(builtinSet.frame());
            HashSet<Term> elements = new HashSet<Term>(
                    ((BuiltinSet) super.transform(builtinSet)).elements());
            elements.addAll(((BuiltinSet) term).elements());
            BuiltinSet returnSet = ((BuiltinSet) term).hasFrame() ?
                    new BuiltinSet(elements, ((BuiltinSet) term).frame()) : new BuiltinSet(elements);
            boundVariables.remove(builtinSet.frame());
            return returnSet;
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
                    kSequence = new KSequence(builder.build(), fragment.frame());
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
