// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.builtin.KLabels;
import org.kframework.backend.java.utils.BitSet;

import java.util.List;
import java.util.stream.Collectors;


/**
 * Class representing an associative list.
 */
public class BuiltinList extends Collection implements CollectionInternalRepresentation {

    /**
     * Flattened list of children.
     */
    public final ImmutableList<Term> children;
    public final Sort sort;
    public final KLabelConstant operatorKLabel;
    public final KLabelConstant unitKLabel;
    private final GlobalContext global;

    private final ElementTailSplit elementTailSplits[];

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

        elementTailSplits = new ElementTailSplit[children.size()];
    }

    /**
     * Class representation of the element and the tail components of a list child.
     * This representation enables efficient matching of head/tail patterns.
     * A list child can be a list element, a list variable, or a disjunction of list elements and variables.
     * The element component consists of the element or the elements in the disjunction, combined with their respective bitsets.
     * The tail component consists of the list variable or the list variables in the disjunction such that the list is empty on the remaining positions,
     * combined with their respective bitsets.
     */
    public static class ElementTailSplit {
        public final Term element;
        public final BitSet elementMask;
        public final Term tail;
        public final BitSet tailMask;
        public final BitSet combinedMask;

        private ElementTailSplit(Term element, BitSet elementMask, Term tail, BitSet tailMask) {
            this.element = element;
            this.elementMask = elementMask;
            this.tail = tail;
            this.tailMask = tailMask;
            combinedMask = elementMask.clone();
            combinedMask.or(tailMask);
        }
    }

    /**
     * Returns the element component and the tail component of the list child on position index.
     */
    public ElementTailSplit splitElementTail(int index, int bitSetLength) {
        if (elementTailSplits[index] == null) {
            BitSet emptyListMask = BitSet.apply(bitSetLength);
            emptyListMask.makeOnes(bitSetLength);
            for (int i = index + 1; i < children.size(); i++) {
                if (children.get(i) instanceof RuleAutomatonDisjunction) {
                    emptyListMask.and(((RuleAutomatonDisjunction) children.get(i)).assocDisjunctionArray[sort.ordinal()].stream()
                            .filter(p -> p.getLeft().isEmpty())
                            .map(p -> p.getRight())
                            .findAny().orElseGet(() -> BitSet.apply(bitSetLength)));

                    if (emptyListMask.isEmpty()) {
                        break;
                    }
                } else {
                    emptyListMask = BitSet.apply(bitSetLength);
                    break;
                }
            }

            if (isElement(index)) {
                BitSet elementMask = BitSet.apply(bitSetLength);
                elementMask.makeOnes(bitSetLength);
                elementTailSplits[index] = new ElementTailSplit(
                        children.get(index),
                        elementMask,
                        Bottom.BOTTOM,
                        BitSet.apply(bitSetLength));
            } else if (isListVariable(children.get(index))) {
                elementTailSplits[index] = new ElementTailSplit(
                        Bottom.BOTTOM,
                        BitSet.apply(bitSetLength),
                        children.get(index),
                        emptyListMask);
            } else if (children.get(index) instanceof RuleAutomatonDisjunction) {
                RuleAutomatonDisjunction elementAutomatonDisjunction = new RuleAutomatonDisjunction(
                        ((RuleAutomatonDisjunction) children.get(index)).disjunctions().stream()
                                .filter(p -> isElement(p.getLeft()))
                                .collect(Collectors.toList()),
                        global);
                BitSet elementMask = BitSet.apply(bitSetLength);
                elementAutomatonDisjunction.disjunctions().stream()
                        .map(p -> p.getRight())
                        .forEach(s -> elementMask.or(s));

                RuleAutomatonDisjunction tailAutomatonDisjunction = new RuleAutomatonDisjunction(
                        ((RuleAutomatonDisjunction) children.get(index)).disjunctions().stream()
                                .filter(p -> !isElement(p.getLeft()))
                                .collect(Collectors.toList()),
                        global);
                BitSet tailMask = BitSet.apply(bitSetLength);
                tailAutomatonDisjunction.disjunctions().stream()
                        .map(p -> p.getRight())
                        .forEach(s -> tailMask.or(s));
                tailMask.and(emptyListMask);

                elementTailSplits[index] = new ElementTailSplit(
                        elementAutomatonDisjunction,
                        elementMask,
                        tailAutomatonDisjunction,
                        tailMask);
            } else {
                assert false : "unexpected class type for builtin list " + children.get(index).getClass();
            }
        }

        return elementTailSplits[index];
    }

    public boolean isElement(int index) {
        return isElement(children.get(index));
    }

    private boolean isElement(Term term) {
        //assert global.getDefinition().subsorts().isSubsortedEq(sort, term.sort());
        //TODO: restore the assertion after fixing variables _:K generated fom ...
        return !(isListVariable(term)
                || term instanceof BuiltinList && ((BuiltinList) term).sort.equals(sort)
                || term instanceof RuleAutomatonDisjunction && ((RuleAutomatonDisjunction) term).disjunctions().stream().anyMatch(p -> !isElement(p.getLeft()))
                || term instanceof KItem && KLabels.KREWRITE.equals(((KItem) term).kLabel()) && !isElement(((KList) ((KItem) term).kList()).get(0)));
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
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public JavaSymbolicObject accept(Transformer transformer) {
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

    public static Term stripListItem(Term term) {
        if (term instanceof KItem) {
            KItem kitem = (KItem) term;
            if (KLabels.ListItem.equals(kitem.klabel())) {
                return ((KList) kitem.kList()).getContents().get(0);
            }
        }
        return term;
    }

    public static Builder builder(Sort sort, KLabelConstant operatorKLabel, KLabelConstant unitKLabel, GlobalContext global) {
        return new Builder(sort, operatorKLabel, unitKLabel, global);
    }

    public static Builder builder(GlobalContext global) {
        return builder(
                Sort.LIST,
                KLabelConstant.of(KLabels.List, global.getDefinition()),
                KLabelConstant.of(KLabels.DotList, global.getDefinition()),
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
                //assert global.getDefinition().subsorts().isSubsortedEq(sort, term.sort()) :
                //        "unexpected term: " + term + " of sort " + term.sort() + " added to list of sort " + sort;
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

    /**
     * Wraps this element in a {@link SingletonBuiltinList}.
     * {@link org.kframework.backend.java.symbolic.FastRuleMatcher} is the only class allowed to call this method.
     */
    public SingletonBuiltinList upElementToList(Term element) {
        return new SingletonBuiltinList(element, global, sort, operatorKLabel, unitKLabel);
    }

    /**
     * Class representation of a singleton builtin list. This representation is not canonical;
     * {@link BuiltinList#builder(Sort, KLabelConstant, KLabelConstant, GlobalContext)} returns the element directly as the canonical representation.
     * {@link org.kframework.backend.java.symbolic.FastRuleMatcher} is the only class allowed to use this class.
     */
    public static class SingletonBuiltinList extends BuiltinList {
        private SingletonBuiltinList(Term child, GlobalContext global, Sort sort, KLabelConstant operatorKLabel, KLabelConstant unitKLabel) {
            super(ImmutableList.of(child), sort, operatorKLabel, unitKLabel, global);
        }
    }

}
