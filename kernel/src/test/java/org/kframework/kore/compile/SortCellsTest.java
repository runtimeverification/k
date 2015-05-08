// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.junit.Assert;
import org.junit.Test;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;

import static org.kframework.kore.KORE.*;

/**
 * Rearrange partially-completed cells to follow the productions declaring them.
 *
 * The main complexity here is eliminating cell fragment variables that might
 * capture multiple cells. In the general case a variable needs to be
 * replaced under cells with separate variables in several slots of the
 * parent and in other places with an appropriate bag expression.
 */
public class SortCellsTest {

    ConfigurationInfo cfgInfo = new TestConfiguration() {{
        addCell(null, "TopCell", "<top>");
        addCell("TopCell", "ThreadCell", "<t>", Multiplicity.STAR);
        addCell("ThreadCell", "KCell", "<k>", Sorts.K());
        addCell("ThreadCell", "EnvCell", "<env>", Sort("Map"));
        addCell("ThreadCell", "OptCell", "<opt>", Multiplicity.OPTIONAL, Sorts.K());
        addUnit("OptCell", KApply(KLabel(".OptCell")));
        addUnit("ThreadCell", KApply(KLabel(".ThreadCellBag")));
        addConcat("ThreadCell", KLabel("_ThreadCellBag_"));
    }};
    LabelInfo labelInfo = new LabelInfo() {{
        addLabel("TopCell", "<top>");
        addLabel("ThreadCell", "<t>");
        addLabel("KCell", "<k>");
        addLabel("EnvCell", "<env>");
        addLabel("OptCell", "<opt>");
    }};

    @Test
    public void testSimpleSplitting() {
        K term = KRewrite(cell("<t>",cell("<env>"),KVariable("X"), KVariable("Y", Att().add(Attribute.SORT_KEY, "OptCell"))),KVariable("X"));
        K expected = KRewrite(cell("<t>",KVariable("X"),cell("<env>"), KVariable("Y", Att().add(Attribute.SORT_KEY, "OptCell"))),KVariable("X"));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testUselessVariable() {
        K term = cell("<t>", cell("<env>"), cell("<k>"), cell("<opt>"), KVariable("X"));
        K expected = cell("<t>", cell("<k>"), cell("<env>"), cell("<opt>"));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testMultipleSplit() {
        K term = KRewrite(cell("<t>", KVariable("X")), KVariable("Y"));
        K expected = KRewrite(cell("<t>", KVariable("_0"), KVariable("_1"), KVariable("_2")), KVariable("Y"));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testAddOptCell() {
        K term = cell("<t>", KVariable("X"), KRewrite(cells(), cell("<opt>")));
        K expected = cell("<t>", KVariable("_0"), KVariable("_1"), KRewrite(KApply(KLabel(".OptCell")), cell("<opt>")));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testRemoveOptCell() {
        K term = cell("<t>", KVariable("X"), KRewrite(cell("<opt>"), cells()));
        K expected = cell("<t>", KVariable("_0"), KVariable("_1"), KRewrite(cell("<opt>"), KApply(KLabel(".OptCell"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testAddStarCell() {
        K term = cell("<top>", KRewrite(cells(), cell("<t>", KVariable("X"))));
        K expected = cell("<top>", KRewrite(KApply(KLabel(".ThreadCellBag")), cell("<t>", KVariable("_0"), KVariable("_1"), KVariable("_2"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testRemoveStarCell() {
        K term = cell("<top>", KRewrite(cell("<t>", KVariable("X")), cells()));
        K expected = cell("<top>", KRewrite(cell("<t>", KVariable("_0"), KVariable("_1"), KVariable("_2")), KApply(KLabel(".ThreadCellBag"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }


    @Test
    public void testConcatStarCell() {
        K term = cell("<top>", KRewrite(KVariable("Y"), cells(KVariable("Y"), cell("<t>", KVariable("X")))));
        K expected = cell("<top>", KRewrite(KVariable("Y"), KApply(KLabel("_ThreadCellBag_"), KApply(KLabel("_ThreadCellBag_"), KApply(KLabel(".ThreadCellBag")), KVariable("Y")), cell("<t>", KVariable("_0"), KVariable("_1"), KVariable("_2")))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
