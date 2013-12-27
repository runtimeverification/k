package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.Set;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;


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

    private final ListMultimap<String, Cell> cells;
    private final boolean isStar;

    public CellCollection(ListMultimap<String, Cell> cells, Variable frame, boolean isStar) {
        super(frame, Kind.CELL_COLLECTION);
        this.cells = ArrayListMultimap.create(cells);
        this.isStar = isStar;

        assert !isStar || cells.keySet().size() <= 1;
        for (String label : cells.keySet()) {
            assert isStar || cells.get(label).size() == 1;
        }
    }

    public CellCollection(Variable frame) {
        this(ArrayListMultimap.<String, Cell>create(), frame, false);
    }

    public CellCollection(ListMultimap<String, Cell> cells, boolean star) {
        this(cells, null, star);
    }

    public CellCollection() {
        this(ArrayListMultimap.<String, Cell>create(), null, false);
    }

    public java.util.Collection<Cell> cells() {
        return cells.values();
    }

    public ListMultimap<String, Cell> cellMap() {
        return cells;
    }

    public boolean containsKey(String label) {
        return cells.containsKey(label);
    }

    public java.util.Collection<Cell> get(String label) {
        return cells.get(label);
    }

    public boolean isStar() {
        return isStar;
    }

    public Set<String> labelSet() {
        return cells.keySet();
    }

    public int size() {
        return cells.size();
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
        return super.equals(collection) && cells.equals(collection.cells);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + (super.frame == null ? 0 : super.frame.hashCode());
        hash = hash * Utils.HASH_PRIME + cells.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        for (Cell cell : cells.values()) {
            stringBuilder.append(cell);
        }
        if (super.hasFrame()) {
            stringBuilder.append(super.frame());
        }
        return stringBuilder.toString();
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}
