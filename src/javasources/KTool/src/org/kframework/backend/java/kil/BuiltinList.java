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
        super(null, Kind.KITEM);
        this.elementsLeft = elementsLeft;
        this.elementsRight = elementsRight;
        this.baseTerms = baseTerms;
        this.baseTermTypes = baseTermTypes;
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

    @Override
    public int size() {
        return elementsLeft.size() + elementsRight.size();
    }

    @Override
    public final boolean isConcreteCollection() {
        return baseTerms.isEmpty();
    }

    @Override
    public boolean isLHSView() {
        return baseTerms.isEmpty() || baseTerms.size() == 1
                && (baseTerms.get(0) instanceof Variable);
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
    protected boolean computeHasCell() {
        boolean hasCell = false;
        for (Term term : elementsLeft) {
            hasCell = hasCell || term.hasCell();
            if (hasCell) {
                return true;
            }
        }
        for (Term term : elementsRight) {
            hasCell = hasCell || term.hasCell();
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

    private enum BuilderStatus {
        ELEMENTS_LEFT, BASE_TERMS, ELEMENTS_RIGHT;
    }

    public static class Builder {

        private BuilderStatus status = BuilderStatus.ELEMENTS_LEFT;

        private ImmutableList.Builder<Term> elementsLeftBuilder = new ImmutableList.Builder<>();
        private ImmutableList.Builder<Term> baseTermsBuilder = new ImmutableList.Builder<>();
        private ImmutableList.Builder<Term> elementsRightBuilder = new ImmutableList.Builder<>();
        private ImmutableList.Builder<BaseTermType> baseTermTypesBuilder = new ImmutableList.Builder<>();

        /**
         * Adds new list item to this builder.
         */
        public void addItem(Term term) {
            if (status == BuilderStatus.BASE_TERMS) {
                status = BuilderStatus.ELEMENTS_RIGHT;
            }

            if (status == BuilderStatus.ELEMENTS_LEFT) {
                elementsLeftBuilder.add(term);
            } else {
                elementsRightBuilder.add(term);
            }
        }

        /**
         * Adds new list items to this builder.
         */
        public void addItems(List<Term> terms) {
            for (Term term : terms) {
                addItem(term);
            }
        }

        private void addConcatTerm(Term term) {
            if (status == BuilderStatus.ELEMENTS_LEFT) {
                status = BuilderStatus.BASE_TERMS;
            } else if (status == BuilderStatus.ELEMENTS_RIGHT) {
                assert false : "builder only allowed to concatencate list terms in: " + BuilderStatus.BASE_TERMS;
            }

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
                assert false : "unexpected concatenated term" + term;
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

            if (term instanceof BuiltinList && status == BuilderStatus.ELEMENTS_LEFT) {
                BuiltinList list = (BuiltinList) term;
                addItems(list.elementsLeft);
                addConcatTerms(list.baseTerms);
                if (status == BuilderStatus.BASE_TERMS) {
                    if (!list.elementsRight.isEmpty()) {
                        addItem(new BuiltinList(list.elementsRight));
                    }
                } else {
                    addItems(list.elementsRight());
                }
            } else {
                addConcatTerm(term);
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
            BuiltinList builtinList = new BuiltinList(
                    elementsLeftBuilder.build(),
                    baseTermsBuilder.build(),
                    elementsRightBuilder.build(),
                    baseTermTypesBuilder.build());

            /* special case: only one List variable */
            if (builtinList.size() == 0 && builtinList.baseTerms.size() == 1) {
                Term base = builtinList.baseTerms.get(0);
                if (base instanceof Variable && base.sort().equals(Sort.LIST)) {
                    return base;
                }
            }
            return builtinList;
        }
    }

}
