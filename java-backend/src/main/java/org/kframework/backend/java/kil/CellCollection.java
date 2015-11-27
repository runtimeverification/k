// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableListMultimap;
import com.google.common.collect.ImmutableMultiset;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Multiset;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.DataStructureSort.Label;
import org.kframework.utils.errorsystem.KEMException;

import java.io.Serializable;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * Represents a collection of cells. The ordering of the internal cells
 * is fixed and agrees with the ordering of the cells used to construct this
 * cell collection.
 *
 * @author AndreiS
 *
 */
public class CellCollection extends Collection implements CollectionInternalRepresentation {

    public static class Cell implements Serializable {
        private final CellLabel cellLabel;
        private Term content;

        public Cell(CellLabel cellLabel, Term content) {
            this.cellLabel = cellLabel;
            this.content = content;
        }

        public CellLabel cellLabel() {
            return cellLabel;
        }

        public Term content() {
            return content;
        }

        public void setContent(Term content) {
            this.content = content;
        }

        @Override
        public boolean equals(Object object) {
            if (this == object) {
                return true;
            }

            if (!(object instanceof Cell)) {
                return false;
            }

            Cell cell = (Cell) object;
            return cellLabel.equals(cell.cellLabel) && content.equals(cell.content);
        }

        @Override
        public int hashCode() {
            int hashCode = 1;
            hashCode = hashCode * Constants.HASH_PRIME + cellLabel.hashCode();
            hashCode = hashCode * Constants.HASH_PRIME + content.hashCode();
            return hashCode;
        }

        @Override
        public String toString() {
            return "<" + cellLabel() + ">" + content + "</" + cellLabel() + ">";
        }
    }

    /**
     * Choose {@code ListMultimap} over {@code SetMultimap} because we need to
     * be able to store identical cells.
     */
    private final ListMultimap<CellLabel, Cell> cells;

    private final Multiset<Variable> collectionVariables;

    /**
     * Specifies if the explicit content of this cell collection contains
     * multiplicity cell.
     */
    // TODO(AndreiS): handle multiplicity='+'
    private final boolean hasMultiplicityCell;

    private final org.kframework.kore.Sort cellSort;

    private final Definition definition;

    public static CellCollection empty(org.kframework.kore.Sort collectionSort, Definition definition) {
        return (CellCollection) builder(collectionSort, definition).build();
    }

    public static CellCollection singleton(
            CellLabel cellLabel, Term content,
            org.kframework.kore.Sort collectionSort, Definition definition) {
        return (CellCollection) builder(collectionSort, definition).put(cellLabel, content).build();
    }

    /**
     * Static helper method which creates canonicalized cell collection
     * according to the given contents.
     */
    public static Term of(
            ListMultimap<CellLabel, Cell> cells, Variable frame,
            org.kframework.kore.Sort collectionSort, Definition definition) {
        Builder builder = builder(collectionSort, definition);
        builder.putAll(cells);
        if (frame != null) {
            builder.concatenate(frame);
        }
        return builder.build();
    }

    private CellCollection(
            ListMultimap<CellLabel, Cell> cells,
            Multiset<Variable> collectionVariables,
            org.kframework.kore.Sort cellSort,
            Definition definition) {
        this(cells, collectionVariables, numOfMultiplicityCellLabels(cells, definition) > 0, cellSort, definition);
    }

    private CellCollection(
            ListMultimap<CellLabel, Cell> cells,
            Multiset<Variable> collectionVariables,
            boolean hasMultiplicityCell,
            org.kframework.kore.Sort cellSort,
            Definition definition) {
        super(computeFrame(collectionVariables), Kind.CELL_COLLECTION);
        this.cells = cells;
        this.collectionVariables = collectionVariables;
        this.hasMultiplicityCell = hasMultiplicityCell;
        this.cellSort = cellSort;
        this.definition = definition;
    }

    private static Variable computeFrame(Multiset<Variable> collectionVariables) {
        return collectionVariables.size() == 1 ? collectionVariables.iterator().next() : null;
    }

    private static int numOfMultiplicityCellLabels(ListMultimap<CellLabel, Cell> cells, Definition definition) {
        int count = 0;
        for (CellLabel cellLabel : cells.keySet()) {
            if (definition.cellMultiplicity(cellLabel) == ConfigurationInfo.Multiplicity.STAR) {
                count++;
            } else {
                if (cells.get(cellLabel).size() != 1) {
                    throw KEMException.criticalError("Cell label " + cellLabel + " does not have "
                            + "multiplicity='*', but multiple cells found: " + cells.get(cellLabel)
                            + "\nExamine the last rule applied to determine the source of the error.");
                }
            }
        }

        assert count <= 1 :
            "Multiple types of starred cells in one cell collection not supported at present";
        return count;
    }

    public ListMultimap<CellLabel, Cell> cells() {
        return cells;
    }

    private Multiset<Cell> values;

    public Multiset<Cell> values() {
        Multiset<Cell> v = values;
        if (v == null) {
            v = ImmutableMultiset.copyOf(cells.values());
            values = v;
        }
        return v;
    }

    public Multiset<Term> baseTerms() {
        return (Multiset<Term>) (Object) collectionVariables();
    }

    public Multiset<Variable> collectionVariables() {
        return collectionVariables;
    }

    public boolean containsLabel(CellLabel label) {
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
    public boolean hasMultiplicityCell() {
        return hasMultiplicityCell;
    }

    public org.kframework.kore.Sort cellSort() {
        return cellSort;
    }

    public Set<CellLabel> labelSet() {
        return cells.keySet();
    }

    /**
     * Builds a new {@code CellCollection} by removing all the given cell
     * labels.
     */
    public Term removeAll(Set<CellLabel> removeLabels) {
        Builder builder = builder();
        cells.keySet().stream()
                .filter(label -> !removeLabels.contains(label))
                .forEach(label -> builder.addAll(cells.get(label)));
        builder.concatenate(collectionVariables);
        return builder.build();
    }

    @Override
    public boolean isEmpty() {
        return cells.isEmpty() && isConcreteCollection();
    }

    @Override
    public int concreteSize() {
        return cells.size();
    }

    @Override
    public final boolean isConcreteCollection() {
        return collectionVariables.isEmpty();
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public List<Term> getKComponents() {
        return cells.values().stream()
                .map(c -> new KItem(
                        KLabelConstant.of(c.cellLabel.name(), definition),
                        KList.concatenate(c.content),
                        sort(),
                        true))
                .collect(Collectors.toList());
    }

    @Override
    public KLabel constructorLabel() {
        org.kframework.kore.KLabel kLabel = definition.configurationInfo().getConcat(cellSort);
        return KLabelConstant.of(kLabel.name(), definition);
    }

    @Override
    public Term unit() {
        org.kframework.kore.KApply kApply = definition.configurationInfo().getUnit(cellSort);
        return new KItem(
                KLabelConstant.of(kApply.klabel().name(), definition),
                KList.EMPTY,
                sort(),
                true);
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
        return collectionVariables.equals(collection.collectionVariables)
                && values().equals(collection.values());
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Constants.HASH_PRIME + collectionVariables.hashCode();
        hashCode = hashCode * Constants.HASH_PRIME + values().hashCode();
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
                stringBuilder
                        .append("<").append(cell.cellLabel()).append(">")
                        .append(cell.content())
                        .append("</").append(cell.cellLabel()).append(">");
            }
            Iterator<Term> iter = baseTerms().iterator();
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
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    public Builder builder() {
        return new Builder(cellSort, definition);
    }

    public static Builder builder(org.kframework.kore.Sort cellSort, Definition definition) {
        return new Builder(cellSort, definition);
    }

    public static class Builder {
        private final ImmutableListMultimap.Builder<CellLabel, Cell> cellsBuilder;
        private final ImmutableMultiset.Builder<Variable> collectionVariablesBuilder;
        private final org.kframework.kore.Sort cellSort;
        private final Definition definition;

        private Builder(org.kframework.kore.Sort cellSort, Definition definition) {
            this.cellSort = cellSort;
            this.definition = definition;
            cellsBuilder = ImmutableListMultimap.builder();
            collectionVariablesBuilder = ImmutableMultiset.builder();
        }

        public Builder add(Cell cell) {
            cellsBuilder.put(cell.cellLabel(), cell);
            return this;
        }

        public Builder addAll(Iterable<Cell> cells) {
            for (Cell cell : cells) {
                add(cell);
            }
            return this;
        }

        public Builder put(CellLabel cellLabel, Term content) {
            cellsBuilder.put(cellLabel, new Cell(cellLabel, content));
            return this;
        }

        public Builder putAll(ListMultimap<CellLabel, Cell> cellMap) {
            cellsBuilder.putAll(cellMap);
            return this;
        }

        public Builder concatenate(Term term) {
            if (term instanceof CellCollection) {
                CellCollection cellCollection = (CellCollection) term;
                cellsBuilder.putAll(cellCollection.cells);
                collectionVariablesBuilder.addAll(cellCollection.collectionVariables);
            } else if (term instanceof Variable && term.kind == Kind.CELL_COLLECTION) {
                collectionVariablesBuilder.add((Variable) term);
            } else {
                assert false : "unexpected concatenated term " + term;
            }
            return this;
        }

        public Builder concatenate(Term... terms) {
            for (Term term : terms) {
                concatenate(term);
            }
            return this;
        }

        public Builder concatenate(Iterable<? extends Term> terms) {
            for (Term term : terms) {
                concatenate(term);
            }
            return this;
        }

        public Term build() {
            ImmutableListMultimap<CellLabel, Cell> cells = cellsBuilder.build();
            ImmutableMultiset<Variable> collectionVariables = collectionVariablesBuilder.build();
            if (cells.isEmpty()) {
                switch (collectionVariables.size()) {
                    case 1:  return collectionVariables.iterator().next();
                    default: return new CellCollection(cells, collectionVariables, cellSort, definition);
                }
            } else {
                return new CellCollection(cells, collectionVariables, cellSort, definition);
            }
        }
    }

}
