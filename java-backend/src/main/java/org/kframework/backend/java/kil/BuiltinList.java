// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.kil.ASTNode;

import java.util.List;


/**
 * Class representing an associative list.
 */
public class BuiltinList extends Collection implements KItemCollection {

    /**
     * Flattened list of children.
     */
    public final ImmutableList<Term> children;
    public final Sort sort;
    public final KLabelConstant operatorKLabel;
    public final KLabelConstant unitKLabel;
    private final GlobalContext global;

    /**
     * Private constructor used by {@link BuiltinList.Builder}.
     */
    private BuiltinList(
            ImmutableList<Term> children,
            Sort sort,
            KLabelConstant operatorKLabel,
            KLabelConstant unitKLabel,
            GlobalContext global)  {
        super(null, Kind.KITEM);
        this.children = children;
        this.sort = sort;
        this.operatorKLabel = operatorKLabel;
        this.unitKLabel = unitKLabel;
        this.global = global;
    }

    public static Term concatenate(GlobalContext global, Term... lists) {
        //return new Builder(sort, operatorKLabel, unitKLabel, global).addAll(lists).build();
        throw new UnsupportedOperationException();
    }

    public boolean isElement(int index) {
        assert global.getDefinition().subsorts().isSubsortedEq(sort, children.get(index).sort());
        return global.getDefinition().subsorts().isSubsorted(sort, children.get(index).sort());
    }

    public Term range(int beginIndex, int endIndex) {
        return BuiltinList.builder(sort, operatorKLabel, unitKLabel, global)
                .addAll(children.subList(beginIndex, endIndex))
                .build();
    }

    public boolean contains(Term term) {
        return children.contains(term);
    }

    public Term get(int index) {
        return children.get(index);
    }

    public int size() {
        return children.size();
    }

    @Override
    public ImmutableList<Variable> collectionVariables() {
        throw new AssertionError("Unimplemented");
    }

    @Override
    public int concreteSize() {
        throw new AssertionError("Unimplemented");
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
        return sort;
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
        return children.equals(list.children)
                && sort.equals(list.sort)
                && operatorKLabel.equals(list.operatorKLabel)
                && unitKLabel.equals(list.unitKLabel);
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Constants.HASH_PRIME + children.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        return false;
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
    public List<Term> getKComponents() {
        return children;
    }

    @Override
    public GlobalContext globalContext() {
        return global;
    }

    public static Builder builder(Sort sort, KLabelConstant operatorKLabel, KLabelConstant unitKLabel, GlobalContext global) {
        return new Builder(sort, operatorKLabel, unitKLabel, global);
    }

    public static Builder builder(GlobalContext global) {
        return builder(
                Sort.LIST,
                KLabelConstant.of("'_List_", global.getDefinition()),
                KLabelConstant.of(".List", global.getDefinition()),
                global);
    }

    public static class Builder {

        private final ImmutableList.Builder<Term> childrenBuilder = new ImmutableList.Builder<>();
        private final Sort sort;
        private final KLabelConstant operatorKLabel;
        private final KLabelConstant unitKLabel;
        private final GlobalContext global;

        public Builder(Sort sort, KLabelConstant operatorKLabel, KLabelConstant unitKLabel, GlobalContext global) {
            this.sort = sort;
            this.operatorKLabel = operatorKLabel;
            this.unitKLabel = unitKLabel;
            this.global = global;
        }

        public Builder add(Term term) {
            if (term instanceof BuiltinList && sort.equals(term.sort())
                    && operatorKLabel.equals(((BuiltinList) term).operatorKLabel)
                    && unitKLabel.equals(((BuiltinList) term).unitKLabel)) {
                return addAll(((BuiltinList) term).children);
            } else {
                childrenBuilder.add(term);
                return this;
            }
        }

        public Builder addAll(List<Term> terms) {
            terms.forEach(this::add);
            return this;
        }

        public Builder addAll(Term... terms) {
            for (Term term : terms) {
                add(term);
            }
            return this;
        }

        public Term build() {
            BuiltinList builtinList = new BuiltinList(
                    childrenBuilder.build(),
                    sort,
                    operatorKLabel,
                    unitKLabel,
                    global);
            return builtinList.size() == 1 ? builtinList.get(0) : builtinList;
        }
    }

    public BuiltinList upElementToList(Term element) {
        assert global.getDefinition().subsorts().isSubsorted(sort, element.sort());
        return new SingletonBuiltinList(element, global, sort, operatorKLabel, unitKLabel);
    }

    private static class SingletonBuiltinList extends BuiltinList {
        private SingletonBuiltinList(Term child, GlobalContext global, Sort sort, KLabelConstant operatorKLabel, KLabelConstant unitKLabel) {
            super(ImmutableList.of(child), sort, operatorKLabel, unitKLabel, global);
        }
    }

}
