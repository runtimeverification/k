// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import java.util.List;

import org.apache.commons.collections4.ListUtils;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import com.google.common.base.Function;
import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Iterables;
import com.google.common.collect.Lists;


/**
 * Class representing a list.
 *
 * @author: YilongL
 */
public class BuiltinList extends Collection {

    public static final BuiltinList EMPTY_LIST = (BuiltinList) builder().build();

    private static enum BaseTermType {
        VARIABLE, FUNCTION, PATTERN, LIST;
    }

    private final ImmutableList<Term> elementsLeft;
    private final ImmutableList<Term> elementsRight;
    private final ImmutableList<Term> baseTerms;
    private final ImmutableList<BaseTermType> baseTermTypes;

    /**
     * Private efficient constructor used by {@link BuiltinList.Builder}.
     */
    private BuiltinList(
            ImmutableList<Term> elementsLeft,
            ImmutableList<Term> baseTerms,
            ImmutableList<Term> elementsRight,
            ImmutableList<BaseTermType> baseTermTypes
            ) {
        super(computeFrame(baseTerms), Kind.KITEM);
        this.elementsLeft = elementsLeft;
        this.elementsRight = elementsRight;
        this.baseTerms = baseTerms;
        this.baseTermTypes = baseTermTypes;
    }

    private static Variable computeFrame(List<Term> baseTerms) {
        if (baseTerms.size() == 1 && baseTerms.get(0) instanceof Variable) {
            return (Variable) baseTerms.get(0);
        } else {
            return null;
        }
    }

    private BuiltinList(ImmutableList<Term> elementsLeft) {
        this(elementsLeft, ImmutableList.<Term>of(), ImmutableList.<Term>of(), ImmutableList.<BaseTermType>of());
    }

    public static Term concatenate(Term... lists) {
        Builder builder = new Builder();
        builder.concatenate(lists);
        return builder.build();
    }

    public boolean contains(Term key) {
        return elementsLeft.contains(key) || elementsRight.contains(key);
    }

    public List<Term> elements() {
        return ListUtils.union(elementsLeft, elementsRight);
    }

    public List<Term> elementsLeft() {
        return elementsLeft;
    }

    public List<Term> elementsRight() {
        return elementsRight;
    }

    public List<Term> baseTerms() {
        return baseTerms;
    }

    public BaseTerm getBaseTerm(int index) {
        if (index < 0) {
            index += baseTerms.size();
        }
        return BaseTerm.of(baseTerms.get(index), baseTermTypes.get(index));
    }

    /**
     * TODO(YilongL): implement it properly!
     */
    public boolean isUnifiableByCurrentAlgorithm() {
        return true;
    }

    @Override
    public int concreteSize() {
        return elementsLeft.size() + elementsRight.size();
    }

    @Override
    public final boolean isConcreteCollection() {
        return baseTerms.isEmpty();
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public Sort sort() {
        return Sort.LIST;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinList)) {
            return false;
        }

        BuiltinList list = (BuiltinList) object;
        /* YilongL: the list shall be normalized if the baseTerms is empty;
         * otherwise, the following equality check would be incorrect */
        return elementsLeft.equals(list.elementsLeft)
                && elementsRight.equals(list.elementsRight)
                && baseTerms.equals(list.baseTerms);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + elementsLeft.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + elementsRight.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + baseTerms.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        boolean hasCell = false;
        for (Term term : Iterables.concat(elements(), baseTerms)) {
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

    public Term get(int index) {
        if (index >= 0) {
            return index < elementsLeft.size() ? elementsLeft.get(index) : null;
        } else {
            int idx;
            if (!baseTerms.isEmpty()) {
                idx = elementsRight.size() + index;
                return idx >= 0 ? elementsRight.get(idx) : null;
            } else {
                idx = elementsLeft.size() + index;
                return idx >= 0 ? elementsLeft.get(idx) : null;
            }
        }
    }

    @Override
    public String toString() {
        return toString(" ", ".List");
    }

    /**
     * TODO(YilongL): use Java8 functional features instead
     * @deprecated
     */
    private static final Function<Term, String> ELEMENT_TO_STRING_FUNCTION = new Function<Term, String>() {
        @Override
        public String apply(Term term) {
            return "ListItem(" + term + ")";
        }
    };

    public String toString(String operator, String identity) {
        if (!isEmpty()) {
            return Joiner.on(operator).join(
                    Joiner.on(operator).join(Lists.transform(elementsLeft, ELEMENT_TO_STRING_FUNCTION)),
                    Joiner.on(operator).join(baseTerms),
                    Joiner.on(operator).join(Lists.transform(elementsRight, ELEMENT_TO_STRING_FUNCTION)));
        } else {
            return identity;
        }
    }

    public static Builder builder() {
        return new Builder();
    }

    public static class BaseTerm {
        private final Term term;
        private final BaseTermType type;

        public static BaseTerm of(Term term, BaseTermType type) {
            return new BaseTerm(term, type);
        }

        private BaseTerm(Term term, BaseTermType type) {
            this.term = term;
            this.type = type;
        }

        public Term term() {
            return term;
        }

        public boolean isVariable() {
            return type == BaseTermType.VARIABLE;
        }

        public boolean isFunction() {
            return type == BaseTermType.FUNCTION;
        }

        public boolean isPattern() {
            return type == BaseTermType.PATTERN;
        }

        public boolean isList() {
            return type == BaseTermType.LIST;
        }
    }

    private enum BuilderStatus {
        /**
         * No base term has been added to the builder.
         */
        ELEMENTS_LEFT,

        /**
         * At least one base term (i.e., function, variable, pattern, or list)
         * has been added to the builder and no list item has been added since
         * then.
         */
        BASE_TERMS,

        /**
         * At least one list item has been added to the builder after some base
         * term.
         */
        ELEMENTS_RIGHT;
    }

    public static class Builder {

        private BuilderStatus status = BuilderStatus.ELEMENTS_LEFT;

        /**
         * List of pending elements that are yet to be decided where to go in
         * the {@code BuiltinList} to be built. This field is only valid in
         * {@code BuilderStatus#BASE_TERMS}.
         */
        private final List<Term> pendingElements = Lists.newArrayList();

        private final ImmutableList.Builder<Term> elementsLeftBuilder = new ImmutableList.Builder<>();
        private final ImmutableList.Builder<Term> baseTermsBuilder = new ImmutableList.Builder<>();
        private final ImmutableList.Builder<Term> elementsRightBuilder = new ImmutableList.Builder<>();
        private final ImmutableList.Builder<BaseTermType> baseTermTypesBuilder = new ImmutableList.Builder<>();

        /**
         * Appends the specified term as a list item, namely
         * {@code ListItem(term)}, to the end of the list.
         *
         * @param term
         *            the specified term
         */
        public void addItem(Term term) {
            if (status == BuilderStatus.ELEMENTS_LEFT) {
                elementsLeftBuilder.add(term);
            } else if (status == BuilderStatus.BASE_TERMS) {
                status = BuilderStatus.ELEMENTS_RIGHT;
                elementsRightBuilder.addAll(pendingElements);
                pendingElements.clear();
                elementsRightBuilder.add(term);
            } else {
                elementsRightBuilder.add(term);
            }
        }

        public void addItems(List<Term> terms) {
            for (Term term : terms) {
                addItem(term);
            }
        }

        private void addConcatTerm(Term term) {
            baseTermsBuilder.add(term);
            if (term instanceof BuiltinList) {
                baseTermTypesBuilder.add(BaseTermType.LIST);
            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isPattern()) {
                baseTermTypesBuilder.add(BaseTermType.PATTERN);
            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isFunction()) {
                baseTermTypesBuilder.add(BaseTermType.FUNCTION);
            } else if (term instanceof ListUpdate) {
                baseTermTypesBuilder.add(BaseTermType.FUNCTION);
            } else if (term instanceof Variable) {
                baseTermTypesBuilder.add(BaseTermType.VARIABLE);
            } else {
                assert false : "unexpected concatenated term " + term;
            }
        }

        private void addConcatTerms(List<Term> terms) {
            for (Term term : terms) {
                addConcatTerm(term);
            }
        }

        /**
         * Concatenates a term of sort List to this builder.
         */
        public void concatenate(Term term) {
            assert term.sort().equals(Sort.LIST)
                : "unexpected sort " + term.sort() + " of concatenated term " + term
                + "; expected " + Sort.LIST;

            if (status == BuilderStatus.ELEMENTS_LEFT) {
                if (!(term instanceof BuiltinList)) {
                    status = BuilderStatus.BASE_TERMS;
                    addConcatTerm(term);
                } else {
                    BuiltinList list = (BuiltinList) term;
                    if (list.isConcreteCollection()) {
                        addItems(list.elementsLeft);
                    } else {
                        addItems(list.elementsLeft);
                        status = BuilderStatus.BASE_TERMS;
                        addConcatTerms(list.baseTerms);
                        pendingElements.addAll(list.elementsRight);
                    }
                }
            } else if (status == BuilderStatus.BASE_TERMS) {
                if (!(term instanceof BuiltinList)) {
                    if (!pendingElements.isEmpty()) {
                        addConcatTerm(new BuiltinList(ImmutableList.copyOf(pendingElements)));
                        pendingElements.clear();
                    }
                    addConcatTerm(term);
                } else {
                    BuiltinList list = (BuiltinList) term;
                    if (list.isConcreteCollection()) {
                        pendingElements.addAll(list.elementsLeft);
                    } else {
                        pendingElements.addAll(list.elementsLeft);
                        if (!pendingElements.isEmpty()) {
                            addConcatTerm(new BuiltinList(ImmutableList.copyOf(pendingElements)));
                            pendingElements.clear();
                        }
                        addConcatTerms(list.baseTerms);
                        pendingElements.addAll(list.elementsRight);
                    }
                }
            } else {
                assert false : "the builder is not allowed to concatencate list terms in "
                        + BuilderStatus.ELEMENTS_RIGHT;
            }
        }

        /**
         * Concatenates terms of sort List to this builder.
         */
        public void concatenate(Term... terms) {
            for (Term term : terms) {
                concatenate(term);
            }
        }

        /**
         * Concatenates terms of sort List to this builder.
         */
        public void concatenate(List<Term> terms) {
            for (Term term : terms) {
                concatenate(term);
            }
        }

        public Term build() {
            if (!pendingElements.isEmpty()) {
                elementsRightBuilder.addAll(pendingElements);
                pendingElements.clear();
            }

            BuiltinList builtinList = new BuiltinList(
                    elementsLeftBuilder.build(),
                    baseTermsBuilder.build(),
                    elementsRightBuilder.build(),
                    baseTermTypesBuilder.build());
            return builtinList.hasFrame() && builtinList.concreteSize() == 0 ? builtinList.frame : builtinList;
        }
    }

}
