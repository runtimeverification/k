// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


/**
 * Class representing a set.
 *
 * @author AndreiS
 */
public class BuiltinSet extends AssociativeCommutativeCollection {

    private final ImmutableSet<Term> elements;

    private BuiltinSet(
            ImmutableSet<Term> elements,
            ImmutableMultiset<KItem> collectionPatterns,
            ImmutableMultiset<Term> collectionFunctions,
            ImmutableMultiset<Variable> collectionVariables,
            GlobalContext global) {
        super(collectionPatterns, collectionFunctions, collectionVariables, global);
        this.elements = elements;
    }

    public static Term concatenate(GlobalContext global, Term... sets) {
        Builder builder = new Builder(global);
        builder.concatenate(sets);
        return builder.build();
    }

    /**
     * TODO(YilongL): implement it properly!
     */
    public boolean isUnifiableByCurrentAlgorithm() {
        return true;
    }

    public static boolean isSetUnifiableByCurrentAlgorithm(Term term, Term otherTerm) {
        return term instanceof BuiltinSet
                && ((BuiltinSet) term).isUnifiableByCurrentAlgorithm()
                && otherTerm instanceof BuiltinSet
                && ((BuiltinSet) term).isUnifiableByCurrentAlgorithm();
    }

    public boolean contains(Term element) {
        return elements.contains(element);
    }

    public Set<Term> elements() {
        return elements;
    }

    @Override
    public int concreteSize() {
        return elements.size();
    }

    @Override
    public Sort sort() {
        return Sort.SET;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinSet)) {
            return false;
        }

        BuiltinSet set = (BuiltinSet) object;
        return elements.equals(set.elements)
                && collectionPatterns.equals(set.collectionPatterns)
                && collectionFunctions.equals(set.collectionFunctions)
                && collectionVariables.equals(set.collectionVariables);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Constants.HASH_PRIME + elements.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + collectionPatterns.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + collectionFunctions.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + collectionVariables.hashCode();
        return hashCode;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
        return transformer.transform(this);
    }


    @Override
    public String toString() {
        return toString(" ", ".Set");
    }

    public String toString(String operator, String identity) {
        Joiner joiner = Joiner.on(operator);
        StringBuilder stringBuilder = new StringBuilder();
        joiner.appendTo(stringBuilder, elements);
        joiner.appendTo(stringBuilder, baseTerms());
        if (stringBuilder.length() == 0) {
            stringBuilder.append(identity);
        }
        return stringBuilder.toString();
    }

    @Override
    public List<Term> getKComponents() {
        DataStructureSort sort = global.getDefinition().dataStructureSortOf(sort());

        ArrayList<Term> components = Lists.newArrayList();
        elements.stream().forEach(element ->
                components.add(KItem.of(
                        KLabelConstant.of(sort.elementLabel(), global.getDefinition()),
                        KList.singleton(element),
                        global, element.att())));

        for (Term term : baseTerms()) {
            if (term instanceof BuiltinSet) {
                components.addAll(((BuiltinSet) term).getKComponents());
            } else {
                components.add(term);
            }
        }

        return components;
    }

    public static Builder builder(GlobalContext global) {
        return new Builder(global);
    }

    public static class Builder {

        private final Set<Term> elements = new HashSet<>();
        private final ImmutableMultiset.Builder<KItem> patternsBuilder = new ImmutableMultiset.Builder<>();
        private final ImmutableMultiset.Builder<Term> functionsBuilder = new ImmutableMultiset.Builder<>();
        private final ImmutableMultiset.Builder<Variable> variablesBuilder = new ImmutableMultiset.Builder<>();
        private final GlobalContext global;

        public Builder(GlobalContext global) {
            this.global = global;
        }

        public boolean add(Term element) {
            return elements.add(element);
        }

        public <T extends Term> boolean addAll(Collection<T> elements) {
            // elements refers to the one in the outer class
            return this.elements.addAll(elements);
        }

        public boolean remove(Term element) {
            return elements.remove(element);
        }

        /**
         * Concatenates terms of sort Set to this builder
         */
        public void concatenate(Term... terms) {
            for (Term term : terms) {
                if (!term.sort().equals(Sort.SET)) {
                    throw KEMException.criticalError("unexpected sort "
                            + term.sort() + " of concatenated term " + term
                            + "; expected " + Sort.SET);
                }

                if (term instanceof BuiltinSet) {
                    BuiltinSet set = (BuiltinSet) term;
                    elements.addAll(set.elements);
                    patternsBuilder.addAll(set.collectionPatterns);
                    functionsBuilder.addAll(set.collectionFunctions);
                    variablesBuilder.addAll(set.collectionVariables);
                } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isPattern()) {
                    patternsBuilder.add((KItem) term);
                } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isFunction()) {
                    functionsBuilder.add(term);
                } else if (term instanceof Variable) {
                    variablesBuilder.add((Variable) term);
                } else {
                    throw KEMException.criticalError("unexpected concatenated term" + term);
                }
            }
        }

        public Term build() {
            BuiltinSet builtinSet = new BuiltinSet(
                    ImmutableSet.copyOf(elements),
                    patternsBuilder.build(),
                    functionsBuilder.build(),
                    variablesBuilder.build(),
                    global);
            return builtinSet.baseTerms().size() == 1 && builtinSet.concreteSize() == 0 ?
                    builtinSet.baseTerms().iterator().next() :
                    builtinSet;
        }
    }

}
