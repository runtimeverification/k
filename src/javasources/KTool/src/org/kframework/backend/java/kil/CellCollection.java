package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

import java.util.Set;

import com.google.common.collect.ArrayListMultimap;
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

    private final Multimap<String, Cell> cells;
    
    /**
     * Contains {@code true} if the explicitly specified part of this cell
     * collection contains one or more types of cells whose multiplicity
     * attributes are {@code "*"}'s; otherwise, {@code false}.
     */
    private final boolean hasStar;

    public CellCollection(Multimap<String, Cell> cells, Variable frame, Context context) {
        super(frame, Kind.CELL_COLLECTION);
        this.cells = ArrayListMultimap.create(cells);
        
        int numOfStarredCellTypes = 0;
        for (String cellLabel : cells.keySet()) {
            if (context.getConfigurationStructureMap().get(cellLabel).multiplicity 
                    == org.kframework.kil.Cell.Multiplicity.ANY) {
                numOfStarredCellTypes++;
            } else {
                assert cells.get(cellLabel).size() == 1;
            }
        }

        assert numOfStarredCellTypes <= 1 : 
            "Multiple types of starred cells in one cell collection not supported at present";
        hasStar = numOfStarredCellTypes > 0;
    }

    public CellCollection(Variable frame) {
        this(ArrayListMultimap.<String, Cell>create(), frame, null);
    }

    public CellCollection(Multimap<String, Cell> cells, Context context) {
        this(cells, null, context);
    }

    public CellCollection() {
        this(ArrayListMultimap.<String, Cell>create(), null, null);
    }

    public java.util.Collection<Cell> cells() {
        return cells.values();
    }

    public Multimap<String, Cell> cellMap() {
        return cells;
    }

    public boolean containsKey(String label) {
        return cells.containsKey(label);
    }

    public java.util.Collection<Cell> get(String label) {
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
