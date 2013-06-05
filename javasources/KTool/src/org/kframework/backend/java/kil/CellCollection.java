package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/20/13
 * Time: 7:02 PM
 * To change this template use File | Settings | File Templates.
 */
public class CellCollection extends Collection {

    private final Map<String, Cell> cells;

    public CellCollection(Map<String, Cell> cells, Variable frame) {
        super(frame, Kind.CELL_COLLECTION);
        this.cells = new HashMap<String, Cell>(cells);
    }

    public CellCollection(Variable frame) {
        super(frame, Kind.CELL_COLLECTION);
        cells = new HashMap<String, Cell>();
    }

    public CellCollection(Map<String, Cell> cells) {
        super(null, Kind.CELL_COLLECTION);
        this.cells = new HashMap<String, Cell>(cells);
    }

    public CellCollection() {
        super(null, Kind.CELL_COLLECTION);
        cells = new HashMap<String, Cell>();
    }

    public java.util.Collection<Cell> cells() {
        return cells.values();
    }

    public boolean containsKey(String label) {
        return cells.containsKey(label);
    }

    public Cell get(String label) {
        return cells.get(label);
    }

    public Map<String, Cell> getCells() {
        return cells;
    }

    public Set<String> labelSet() {
        return cells.keySet();
    }

    public int size() {
        return cells.size();
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        for (Cell cell : cells.values()) {
            stringBuilder.append(cell);
        }
        if (super.hasFrame()) {
            stringBuilder.append(super.getFrame());
        }
        return stringBuilder.toString();
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
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
