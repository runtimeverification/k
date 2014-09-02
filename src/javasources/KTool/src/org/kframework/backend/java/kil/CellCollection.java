// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.DataStructureSort.Label;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;


/**
 * Represents a collection of {@link Cell}s. The ordering of the internal cells
 * is fixed and agrees with the ordering of the cells used to construct this
 * cell collection.
 *
 * @author AndreiS
 *
 */
@SuppressWarnings("rawtypes")
public class CellCollection extends Collection {

    /**
     * Choose {@code ListMultimap} over {@code SetMultimap} because we need to
     * be able to store identical cells.
     */
    // TODO(YilongL): make it immutable?
    private final ListMultimap<CellLabel, Cell> cells;

    /**
     * Only allow {@code Variable}s as base terms for now.
     */
    private final Set<Variable> baseTerms;

    /**
     * Contains {@code true} if the explicitly specified part of this cell
     * collection contains one or more types of cells whose multiplicity
     * attributes are {@code "*"}'s; otherwise, {@code false}.
     */
    // TODO(AndreiS): handle multiplicity='+'
    private final boolean hasStar;

    public CellCollection(Multimap<CellLabel, Cell> cells, Variable frame, Context context) {
        super(frame, Kind.CELL_COLLECTION);
        // TODO(YilongL): implement builder pattern for this!
        this.cells = ArrayListMultimap.create(cells);
        this.baseTerms = frame != null ?
                Collections.<Variable>singleton(frame) :
                Collections.<Variable>emptySet();

        this.hasStar = numOfTypesOfStarredSubcells(cells, context) > 0;
    }

    public CellCollection(Multimap<CellLabel, Cell> cells, List<Variable> baseTerms, Context context) {
        super(getFrame(baseTerms), Kind.CELL_COLLECTION);
        this.cells = ArrayListMultimap.create(cells);
        this.baseTerms = ImmutableSet.copyOf(baseTerms);

        this.hasStar = numOfTypesOfStarredSubcells(cells, context) > 0;
    }

    public CellCollection(Variable frame) {
        this(ArrayListMultimap.<CellLabel, Cell>create(), frame, null);
    }

    public CellCollection(Multimap<CellLabel, Cell> cells, Context context) {
        this(cells, (Variable) null, context);
    }

    public CellCollection() {
        this(ArrayListMultimap.<CellLabel, Cell>create(), (Variable) null, null);
    }

    public java.util.Collection<Cell> cells() {
        return cells.values();
    }

    public Multimap<CellLabel, Cell> cellMap() {
        return cells;
    }

    public Set<Variable> baseTerms() {
        return baseTerms;
    }

    public boolean containsKey(CellLabel label) {
        return cells.containsKey(label);
    }

    public java.util.Collection<Cell> get(CellLabel label) {
        return cells.get(label);
    }

    /**
     * Checks if the explicitly specified part of this cell collection contains
     * one or more types of cells whose multiplicity attributes are {@code "*"}
     * 's.
     */
    public boolean hasStar() {
        return hasStar;
    }

    public Set<CellLabel> labelSet() {
        return cells.keySet();
    }

    @Override
    public boolean isEmpty() {
        return cells.isEmpty() && baseTerms.isEmpty();
    }

    @Override
    public int concreteSize() {
        return cells.size();
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
        return kind.asSort();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof CellCollection)) {
            return false;
        }

        CellCollection collection = (CellCollection) object;
        if (!baseTerms.equals(collection.baseTerms)) {
            return false;
        }

        if (cells.keys().equals(collection.cells.keys())) {
            for (CellLabel cellLabel : cells.keySet()) {
                /* YilongL: didn't use the O(N) hash-based approach for
                 * comparing two bags because 1) the fast destructive rewriter
                 * destroys hashcode of terms 2) the number of elements is
                 * usually very small */
                List<Cell> list = Lists.newArrayList(cells.get(cellLabel));
                for (Cell<?> c : collection.cells.get(cellLabel)) {
                    if (!list.remove(c)) {
                        return false;
                    }
                }
            }
            return true;
        } else {
            return false;
        }
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + baseTerms.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + cells.hashCode();
        return hashCode;
    }

    @Override
    protected boolean computeMutability() {
        return true;
    }

    @Override
    public String toString() {
        if (isEmpty()) {
            return DataStructureSort.LABELS.get(org.kframework.kil.Sort.BAG).get(Label.UNIT);
        } else {
            StringBuilder stringBuilder = new StringBuilder();
            for (Cell cell : cells.values()) {
                stringBuilder.append(cell);
            }
            Iterator<Variable> iter = baseTerms.iterator();
            while (iter.hasNext()) {
                stringBuilder.append(iter.next());
                if (iter.hasNext()) {
                    stringBuilder.append(" ");
                }
            }
            return stringBuilder.toString();
        }
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

    private static int numOfTypesOfStarredSubcells(Multimap<CellLabel, Cell> cells, Context context) {
        int count = 0;
        for (CellLabel cellLabel : cells.keySet()) {
            if (context.getConfigurationStructureMap().get(cellLabel.name()).isStarOrPlus()) {
                count++;
            } else {
                assert cells.get(cellLabel).size() == 1:
                        "cell label " + cellLabel + " does not have multiplicity='*', "
                        + "but multiple cells found " + cells;
            }
        }

        assert count <= 1 :
            "Multiple types of starred cells in one cell collection not supported at present";
        return count;
    }

    /**
     * Private helper method that gets the frame variable from a list of base
     * terms.
     *
     * @param baseTerms
     * @return the frame if there is only one variable in the base terms;
     *         otherwise, {@code null}
     */
    private static Variable getFrame(List<Variable> baseTerms) {
        return (baseTerms.size() == 1) ? baseTerms.get(0) : null;
    }

    /**
     * Promotes a given {@link Term} to a given {@link Kind}. The {@code Kind}s
     * involved in this method can only be {@code Kind#CELL} or
     * {@code Kind#CELL_COLLECTION}. If the kind of the given {@code Term} is
     * already above or equal to the target {@code Kind}, do nothing.
     * <p>
     * To be more specific, a {@code Cell} can be promoted to a single-element
     * {@code CellCollection}.
     *
     * @param term
     *            the given term to be promoted
     * @param kind
     *            the target kind that the term is to be promoted to
     * @return the resulting term after kind promotion
     */
    public static Term upKind(Term term, Kind kind, Context context) {
        assert term.kind() == Kind.CELL || term.kind() == Kind.CELL_COLLECTION;
        assert kind == Kind.CELL || kind == Kind.CELL_COLLECTION;

        /* promote Cell to CellCollection */
        if (term.kind() == Kind.CELL && kind == Kind.CELL_COLLECTION) {
            if (term instanceof Cell) {
                Cell cell = (Cell) term;
                Multimap<CellLabel, Cell> cells = ArrayListMultimap.create();
                cells.put(cell.getLabel(), cell);
                return new CellCollection(cells, context);
            } else {
                // do nothing since we cannot simply promote a variable from
                // sort BagItem to Bag
            }
        }

        return term;
    }

    /**
     * Degrades a given {@link Term} to a given {@link Kind}. The {@code Kind}s
     * involved in this method can only be {@code Kind#CELL} or
     * {@code Kind#CELL_COLLECTION}. If the kind of the given {@code Term} is
     * already lower than or equal to the target {@code Kind}, do nothing.
     * <p>
     * To be more specific, a single-element {@code CellCollection} can be
     * degraded to a {@code Cell}.
     *
     * @param term
     *            the given term to be degraded
     * @return the resulting term after kind degradation
     */
    public static Term downKind(Term term) {
        assert term.kind() == Kind.CELL || term.kind() == Kind.CELL_COLLECTION;

        if (term instanceof CellCollection
                && ((CellCollection) term).baseTerms().isEmpty()
                && ((CellCollection) term).concreteSize() == 1) {
            term = ((CellCollection) term).cells().iterator().next();
        }

        // YilongL: do not degrade the kind of a Variable since you cannot
        // upgrade it later

        return term;
    }

}
