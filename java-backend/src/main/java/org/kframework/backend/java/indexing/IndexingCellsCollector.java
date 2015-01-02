// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import java.util.List;
import java.util.Map;

import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.kil.Attribute;
import org.kframework.kil.loader.Constants;

import com.google.common.collect.Lists;

/**
 * Collects indexing cells used in {@link IndexingTable}.
 *
 * @author YilongL
 *
 */
public class IndexingCellsCollector extends BottomUpVisitor {

    private final Definition definition;
    private final List<CellCollection.Cell> indexingCells;

    public static List<CellCollection.Cell> getIndexingCells(Term term, Definition definition) {
        IndexingCellsCollector collector = new IndexingCellsCollector(definition);
        term.accept(collector);
        return collector.indexingCells;
    }

    private IndexingCellsCollector(Definition definition) {
        this.definition = definition;
        this.indexingCells = Lists.newArrayList();
    }

    @Override
    public void visit(CellCollection cellCollection) {
        for (CellCollection.Cell cell : cellCollection.cells().values()) {
            CellLabel cellLabel = cell.cellLabel();
            String streamCellAttr = definition.context()
                    .getConfigurationStructureMap().get(cellLabel.name()).cell
                    .getCellAttribute(Attribute.STREAM_KEY);

            if (cellLabel.equals(CellLabel.K)
                    || Constants.STDIN.equals(streamCellAttr)
                    || Constants.STDOUT.equals(streamCellAttr)
                    || Constants.STDERR.equals(streamCellAttr)) {
                indexingCells.add(cell);
            }

            if (cell.content() instanceof CellCollection) {
                visit((CellCollection) cell.content());
            }
        }
    }
}