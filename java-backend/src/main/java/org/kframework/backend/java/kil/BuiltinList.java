// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.kil.ASTNode;

import java.util.List;


/**
 * Class representing a list.
 */
public class BuiltinList extends Collection implements KItemCollection {

    private enum BaseTermType {
        VARIABLE, FUNCTION, PATTERN, LIST;
    }


    /**
     * Flattenedss list of children.
     */
    public final ImmutableList<Term> children;
    private final GlobalContext global;
    public final Sort sort;
    public final KLabelConstant opKLabel;
    public final KLabelConstant unitKLabel;

    /**
     * Private efficient constructor used by {@link BuiltinList.Builder}.
     */
    private BuiltinList(
            ImmutableList<Term> children,
            GlobalContext global, Sort sort, KLabelConstant opKLabel, KLabelConstant unitKLabel) {
        super(null, Kind.KITEM);
        this.children = children;
        this.global = global;
        this.sort = sort;
        this.opKLabel = opKLabel;
        this.unitKLabel = unitKLabel;
    }

    public static Term concatenate(GlobalContext global, Term... lists) {
        Builder builder = new Builder(global);
        builder.concatenate(lists);
        return builder.build();
    }

    public boolean contains(Term term) {
        return children.contains(term);
    }

    @Override
    public ImmutableList<Variable> collectionVariables() {
        throw new AssertionError("Unimplemented");
    }

    @Override
    public int concreteSize() {
        throw new AssertionError("Unimplemented");
    }

    public int size() {
        return children.size();
    }

    @Override
    public final boolean isConcreteCollection() {
        throw new AssertionError("Unimplemented");
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
        return children.equals(list.children) && sort.equals(list.sort);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Constants.HASH_PRIME + children.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        throw new AssertionError("Unimplemented");
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
       return children.get(index);
    }

    @Override
    public List<Term> getKComponents() {
        return children;
    }

    @Override
    public GlobalContext globalContext() {
        return global;
    }

    public static Builder builder(GlobalContext global) {
        return new Builder(global);
    }

    public static class Builder {
//
//        private BuilderStatus status = BuilderStatus.ELEMENTS_LEFT;
//
//        /**
//         * List of pending elements that are yet to be decided where to go in
//         * the {@code BuiltinList} to be built. This field is only valid in
//         * {@code BuilderStatus#BASE_TERMS}.
//         */
//        private final List<Term> pendingElements = Lists.newArrayList();
//
//        private final ImmutableList.Builder<Term> elementsLeftBuilder = new ImmutableList.Builder<>();
//        private final ImmutableList.Builder<Term> baseTermsBuilder = new ImmutableList.Builder<>();
//        private final ImmutableList.Builder<Term> elementsRightBuilder = new ImmutableList.Builder<>();
//        private final ImmutableList.Builder<BaseTermType> baseTermTypesBuilder = new ImmutableList.Builder<>();
//        private final ImmutableList.Builder<Variable> listVariablesBuilder = new ImmutableList.Builder<>();
//        private final GlobalContext global;
//
        public Builder(GlobalContext global) {
//            this.global = global;
        }
//
//        /**
//         * Appends the specified term as a list item, namely
//         * {@code ListItem(term)}, to the end of the list.
//         *
//         * @param term
//         *            the specified term
//         */
        public void addItem(Term term) {
//            if (status == BuilderStatus.ELEMENTS_LEFT) {
//                elementsLeftBuilder.add(term);
//            } else if (status == BuilderStatus.BASE_TERMS) {
//                status = BuilderStatus.ELEMENTS_RIGHT;
//                elementsRightBuilder.addAll(pendingElements);
//                pendingElements.clear();
//                elementsRightBuilder.add(term);
//            } else {
//                elementsRightBuilder.add(term);
//            }
            throw new AssertionError("Unimplemented");
        }
//
        public void addItems(List<Term> terms) {
//            for (Term term : terms) {
//                addItem(term);
//            }
            throw new AssertionError("Unimplemented");
        }
//
//        private void addConcatTerm(Term term) {
//            baseTermsBuilder.add(term);
//            if (term instanceof BuiltinList) {
//                baseTermTypesBuilder.add(BaseTermType.LIST);
//            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isPattern()) {
//                baseTermTypesBuilder.add(BaseTermType.PATTERN);
//            } else if (term instanceof KItem && ((KLabel) ((KItem) term).kLabel()).isFunction()) {
//                baseTermTypesBuilder.add(BaseTermType.FUNCTION);
//            } else if (term instanceof Variable) {
//                baseTermTypesBuilder.add(BaseTermType.VARIABLE);
//                listVariablesBuilder.add((Variable) term);
//            } else {
//                throw KExceptionManager.criticalError("unexpected concatenated term" + term, term);
//            }
//        }
//
//        private void addConcatTerms(List<Term> terms) {
//            for (Term term : terms) {
//                addConcatTerm(term);
//            }
//        }
//
//        /**
//         * Concatenates a term of sort List to this builder.
//         */
//        public void concatenate(Term term) {
//            if (!term.sort().equals(Sort.LIST)) {
//                throw KEMException.criticalError("unexpected sort "
//                        + term.sort() + " of concatenated term " + term
//                        + "; expected " + Sort.LIST);
//            }
//
//            if (status == BuilderStatus.ELEMENTS_LEFT) {
//                if (!(term instanceof BuiltinList)) {
//                    status = BuilderStatus.BASE_TERMS;
//                    addConcatTerm(term);
//                } else {
//                    BuiltinList list = (BuiltinList) term;
//                    if (list.isConcreteCollection()) {
//                        addItems(list.elementsLeft);
//                    } else {
//                        addItems(list.elementsLeft);
//                        status = BuilderStatus.BASE_TERMS;
//                        addConcatTerms(list.baseTerms);
//                        pendingElements.addAll(list.elementsRight);
//                    }
//                }
//            } else if (status == BuilderStatus.BASE_TERMS) {
//                if (!(term instanceof BuiltinList)) {
//                    if (!pendingElements.isEmpty()) {
//                        addConcatTerm(new BuiltinList(
//                                ImmutableList.copyOf(pendingElements),
//                                global, foo));
//                        pendingElements.clear();
//                    }
//                    addConcatTerm(term);
//                } else {
//                    BuiltinList list = (BuiltinList) term;
//                    if (list.isConcreteCollection()) {
//                        pendingElements.addAll(list.elementsLeft);
//                    } else {
//                        pendingElements.addAll(list.elementsLeft);
//                        if (!pendingElements.isEmpty()) {
//                            addConcatTerm(new BuiltinList(
//                                    ImmutableList.copyOf(pendingElements),
//                                    global, foo));
//                            pendingElements.clear();
//                        }
//                        addConcatTerms(list.baseTerms);
//                        pendingElements.addAll(list.elementsRight);
//                    }
//                }
//            } else {
//                throw KExceptionManager.criticalError(
//                        "the builder is not allowed to concatencate list terms in "
//                        + BuilderStatus.ELEMENTS_RIGHT, term);
//            }
//        }
//
//        /**
//         * Concatenates terms of sort List to this builder.
//         */
        public void concatenate(Term... terms) {
//            for (Term term : terms) {
//                concatenate(term);
//            }
        }
//
        /**
         * Concatenates terms of sort List to this builder.
         */
        public void concatenate(List<Term> terms) {
//            for (Term term : terms) {
//                concatenate(term);
//            }
        }
//
        public Term build() {
//            if (!pendingElements.isEmpty()) {
//                elementsRightBuilder.addAll(pendingElements);
//                pendingElements.clear();
//            }
//
//            BuiltinList builtinList = new BuiltinList(
//                    elementsLeftBuilder.build(),
//                    baseTermsBuilder.build(),
//                    elementsRightBuilder.build(),
//                    baseTermTypesBuilder.build(),
//                    listVariablesBuilder.build(),
//                    global);
//            return builtinList.baseTerms().size() == 1 && builtinList.concreteSize() == 0 ?
//                   builtinList.baseTerms().get(0) :
//                   builtinList;
            throw new AssertionError("Unimplemented");
        }
    }

}
