// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.builtin.KLabels;
import org.kframework.kil.ASTNode;
import org.kframework.utils.BitSet;

import java.util.List;
import java.util.stream.Collectors;


/**
 * Class representing an associative list.
 */
public class BuiltinList extends Collection implements CollectionInternalRepresentation, HasGlobalContext {

    /**
     * Flattened list of children.
     */
    public final ImmutableList<Term> children;
    public final Sort sort;
    public final KLabelConstant operatorKLabel;
    public final KLabelConstant unitKLabel;
    private final GlobalContext global;

    private final BitSet isElementMask[];
    private final BitSet isTailMask[];

    /**
     * Private constructor used by {@link BuiltinList.Builder}.
     */
    private BuiltinList(
            ImmutableList<Term> children,
            Sort sort,
            KLabelConstant operatorKLabel,
            KLabelConstant unitKLabel,
            GlobalContext global) {
        super(null, sort.equals(Sort.KSEQUENCE) ? Kind.K : Kind.KITEM);
        this.children = children;
        this.sort = sort;
        this.operatorKLabel = operatorKLabel;
        this.unitKLabel = unitKLabel;
        this.global = global;

        isElementMask = new BitSet[children.size()];
        isTailMask = new BitSet[children.size()];
    }

    public boolean isElement(int index) {
        return isElement(children.get(index));
    }

    public boolean isElement(int index, BitSet mask) {
        if (isElementMask[index] == null) {
            isElementMask[index] = BitSet.apply(mask.length());
            if (isElement(index)) {
                isElementMask[index].makeOnes(mask.length());
            } else if (children.get(index) instanceof RuleAutomatonDisjunction) {
                ((RuleAutomatonDisjunction) children.get(index)).disjunctions().stream()
                        .filter(p -> isElement(p.getLeft()))
                        .map(p -> p.getRight())
                        .forEach(s -> isElementMask[index].or(s));
            } else {
                assert isListVariable(children.get(index)) || children.get(index) instanceof BuiltinList;
            }
        }

        return mask.subset(isElementMask[index]);
    }

    public boolean isTail(int index, BitSet mask) {
        if (isTailMask[index] == null) {
            isTailMask[index] = BitSet.apply(mask.length());
            if (index != children.size()) {
                if (isListVariable(children.get(index))) {
                    isTailMask[index].makeOnes(mask.length());
                } else if (children.get(index) instanceof RuleAutomatonDisjunction) {
                    ((RuleAutomatonDisjunction) children.get(index)).getVariablesForSort(sort).stream()
                            .map(p -> p.getRight())
                            .forEach(s -> isTailMask[index].or(s));
                } else {
                    assert isElement(index);
                }

                for (int i = index + 1; i < children.size(); i++) {
                    if (children.get(index) instanceof RuleAutomatonDisjunction) {
                        BitSet childEmptyListMask = BitSet.apply(mask.length());
                        ((RuleAutomatonDisjunction) children.get(index)).assocDisjunctionArray[sort.ordinal()].stream()
                                .filter(p -> p.getLeft().isEmpty())
                                .map(p -> p.getRight())
                                .forEach(s -> childEmptyListMask.or(s));
                        isTailMask[index].and(childEmptyListMask);
                        if (isTailMask[index].isEmpty()) {
                            break;
                        }
                    } else {
                        isTailMask[index] = BitSet.apply(mask.length());
                        break;
                    }
                }
            } else {
                isTailMask[index].makeOnes(mask.length());
            }
        }
        return mask.subset(isTailMask[index]);
    }

    private boolean isElement(Term term) {
        //assert global.getDefinition().subsorts().isSubsortedEq(sort, term.sort());
        //TODO: restore the assertion after fixing variables _:K generated fom ...
        return !(isListVariable(term)
                || term instanceof BuiltinList
                || term instanceof RuleAutomatonDisjunction && ((RuleAutomatonDisjunction) term).disjunctions().stream().anyMatch(p -> !isElement(p.getLeft()))
                || term instanceof KItem && ((KItem) term).kLabel().toString().equals(KLabels.KREWRITE) && !isElement(((KList) ((KItem) term).kList()).get(0)));
    }

    private boolean isListVariable(Term term) {
        //TODO: remove Sort.KSEQUENCE case after fixing variables _:K generated fom ...
        return term instanceof Variable && (term.sort().equals(sort) || term.sort().equals(Sort.KSEQUENCE));
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
        return ImmutableList.copyOf(children.stream().filter(e -> !isElement(e)).map(Variable.class::cast).collect(Collectors.toList()));
    }

    @Override
    public int concreteSize() {
        return (int) children.stream().filter(this::isElement).count();
    }

    @Override
    public final boolean isConcreteCollection() {
        return children.stream().allMatch(this::isElement);
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
    public String toString() {
        return !isEmpty() ?
                operatorKLabel + "(" + children.stream().map(Term::toString).collect(Collectors.joining(", ")) + ")" :
                unitKLabel + "()";
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
    public KLabel constructorLabel() {
        return operatorKLabel;
    }

    @Override
    public Term unit() {
        return KItem.of(unitKLabel, KList.concatenate(), global);
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
                KLabelConstant.of("_List_", global.getDefinition()),
                KLabelConstant.of(".List", global.getDefinition()),
                global);
    }

    public static Builder kSequenceBuilder(GlobalContext global) {
        return builder(
                Sort.KSEQUENCE,
                KLabelConstant.of(KLabels.KSEQ, global.getDefinition()),
                KLabelConstant.of(KLabels.DOTK, global.getDefinition()),
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
                //if(!(term instanceof KItem && ((KItem) term).klabel().equals(this.unitKLabel))) // do not add the unit
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
        return new SingletonBuiltinList(element, global, sort, operatorKLabel, unitKLabel);
    }

    private static class SingletonBuiltinList extends BuiltinList {
        private SingletonBuiltinList(Term child, GlobalContext global, Sort sort, KLabelConstant operatorKLabel, KLabelConstant unitKLabel) {
            super(ImmutableList.of(child), sort, operatorKLabel, unitKLabel, global);
        }
    }

}
