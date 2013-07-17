package org.kframework.backend.java.kil;

import com.google.common.collect.HashMultimap;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.Set;

import com.google.common.collect.Multimap;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/20/13
 * Time: 7:02 PM
 * To change this template use File | Settings | File Templates.
 */
public class CellCollection extends Collection {

    private final Multimap<String, Cell> cells;
    private final boolean isStar;

    public CellCollection(Multimap<String, Cell> cells, Variable frame, boolean isStar) {
        super(frame, Kind.CELL_COLLECTION);
        this.cells = HashMultimap.create(cells);
        this.isStar = isStar;

        assert !isStar || cells.keySet().size() <= 1;
        for (String label : cells.keySet()) {
            assert isStar || cells.get(label).size() == 1;
        }
    }

    public CellCollection(Variable frame) {
        this(HashMultimap.<String, Cell>create(), frame, false);
    }

    public CellCollection(Multimap<String, Cell> cells, boolean star) {
        this(cells, null, star);
    }

    public CellCollection() {
        this(HashMultimap.<String, Cell>create(), null, false);
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
