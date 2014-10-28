// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;


/**
 * Class representing a set.
 *
 * @author AndreiS
 */
public class BuiltinSet extends AssociativeCommutativeCollection {

    public static final BuiltinSet EMPTY_SET = new BuiltinSet(
            ImmutableSet.<Term>of(),
            ImmutableMultiset.<KItem>of(),
            ImmutableMultiset.<Term>of(),
            ImmutableMultiset.<Variable>of());

    private final ImmutableSet<Term> elements;

    private BuiltinSet(
            ImmutableSet<Term> elements,
            ImmutableMultiset<KItem> collectionPatterns,
            ImmutableMultiset<Term> collectionFunctions,
            ImmutableMultiset<Variable> collectionVariables) {
        super(collectionPatterns, collectionFunctions, collectionVariables);
        this.elements = elements;
    }

    public static Term concatenate(Term... sets) {
        Builder builder = new Builder();
        builder.concatenate(sets);
        return builder.build();
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
        hashCode = hashCode * Utils.HASH_PRIME + elements.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + collectionPatterns.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + collectionFunctions.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + collectionVariables.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        boolean hasCell = false;
        for (Term term : Iterables.concat(elements, baseTerms())) {
            hasCell = hasCell || term.isMutable();
            if (hasCell) {
                return true;
            }
        }
        return false;
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
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
    protected List<Term> getKComponents(TermContext context) {
        DataStructureSort sort = context.definition().context().dataStructureSortOf(
                sort().toFrontEnd());

        ArrayList<Term> components = Lists.newArrayList();
        elements.stream().forEach(element ->
                components.add(KItem.of(
                        KLabelConstant.of(sort.elementLabel(), context.definition().context()),
                        KList.singleton(element),
                        context)));

        for (Term term : baseTerms()) {
            if (term instanceof BuiltinSet) {
                components.addAll(((BuiltinSet) term).getKComponents(context));
            } else {
                components.add(term);
            }
        }

        return components;
    }

    public static Builder builder() {
        return new Builder();
    }

    public static class Builder {

        private Set<Term> elements = new HashSet<>();
        private ImmutableMultiset.Builder<KItem> patternsBuilder = new ImmutableMultiset.Builder<>();
        private ImmutableMultiset.Builder<Term> functionsBuilder = new ImmutableMultiset.Builder<>();
        private ImmutableMultiset.Builder<Variable> variablesBuilder = new ImmutableMultiset.Builder<>();

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
                    throw KExceptionManager.criticalError("unexpected sort "
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
                } else if (term instanceof SetUpdate) {
                    functionsBuilder.add(term);
                } else if (term instanceof Variable) {
                    variablesBuilder.add((Variable) term);
                } else {
                    throw KExceptionManager.criticalError("unexpected concatenated term" + term);
                }
            }
        }

        public Term build() {
            BuiltinSet builtinSet = new BuiltinSet(
                    ImmutableSet.copyOf(elements),
                    patternsBuilder.build(),
                    functionsBuilder.build(),
                    variablesBuilder.build());
            return builtinSet.baseTerms().size() == 1 && builtinSet.concreteSize() == 0 ?
                    builtinSet.baseTerms().iterator().next() :
                    builtinSet;
        }
    }

}
