package org.kframework.backend.java.kil;

import java.util.Set;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.KSorts;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

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
    // TODO(AndreiS): handle multiplicity='+'
    private final boolean hasStar;

    public CellCollection(Multimap<String, Cell> cells, Variable frame, Context context) {
        super(frame, Kind.CELL_COLLECTION);
        this.cells = ArrayListMultimap.create(cells);
        
        int numOfStarredCellTypes = 0;
        for (String cellLabel : cells.keySet()) {
            if (context.getConfigurationStructureMap().get(cellLabel).isStarOrPlus()) {
                numOfStarredCellTypes++;
            } else {
                assert cells.get(cellLabel).size() == 1:
                        "cell label " + cellLabel + " does not have multiplicity='*', "
                        + "but multiple cells found " + cells;
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

    @Override
    public int size() {
        return cells.size();
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public String sort() {
        return kind.toString();
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
        return (frame == null ? collection.frame == null : frame
                .equals(collection.frame)) && cells.equals(collection.cells);
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + (frame == null ? 0 : frame.hashCode());
            hashCode = hashCode * Utils.HASH_PRIME + cells.hashCode();
        }
        return hashCode;
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
                Multimap<String, Cell> cells = ArrayListMultimap.create();
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
                && !((CellCollection) term).hasFrame()
                && ((CellCollection) term).size() == 1) {
            term = ((CellCollection) term).cells().iterator().next();
        } 
        
        // YilongL: do not degrade the kind of a Variable since you cannot
        // upgrade it later

        return term;
    }

}
