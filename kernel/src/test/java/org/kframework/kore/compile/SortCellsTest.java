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
        K expected = cell("<top>", KRewrite(KVariable("Y"), KApply(KLabel("_ThreadCellBag_"), KVariable("Y"), cell("<t>", KVariable("_0"), KVariable("_1"), KVariable("_2")))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testConcatStarCellEmptyl() {
        K term = cell("<top>", KRewrite(KVariable("Y"), cells()));
        K expected = cell("<top>", KRewrite(KVariable("Y"), KApply(KLabel(".ThreadCellBag"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    @Test
    public void testFragment1() {
        K term = cell("<top>",cell("<t>",KVariable("F")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")), KSequence(KVariable("F"), KVariable("Rest")))), KVariable("F2")));
        K expected = cell("<top>",app("_ThreadCellBag_",
                cell("<t>", KVariable("_0"), KVariable("_1"), KVariable("_2")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")),
                                KSequence(cell("<t>-fragment", KVariable("_0"), KVariable("_1"), KVariable("_2")), KVariable("Rest")))),
                        KVariable("_3"),
                        KVariable("_4"))));
                KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }
    @Test
    public void testFragment2() {
        K term = cell("<top>",cell("<t>",cell("<k>",KVariable("K")),KVariable("F")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")), KSequence(KVariable("F"), KVariable("Rest")))), KVariable("F2")));
        K expected = cell("<top>",app("_ThreadCellBag_",
                cell("<t>", cell("<k>", KVariable("K")), KVariable("_0"), KVariable("_1")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")),
                                KSequence(cell("<t>-fragment", app("noKCell"), KVariable("_0"), KVariable("_1")), KVariable("Rest")))),
                        KVariable("_2"),
                        KVariable("_3"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }
    @Test
    public void testFragment3() {
        K term = cell("<top>",cell("<t>",cell("<opt>",KVariable("O")),KVariable("F")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")), KSequence(KVariable("F"), KVariable("Rest")))), KVariable("F2")));
        K expected = cell("<top>",app("_ThreadCellBag_",
                cell("<t>", KVariable("_0"), KVariable("_1"), cell("<opt>", KVariable("O"))),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")),
                                KSequence(cell("<t>-fragment", KVariable("_0"), KVariable("_1"), app("noOptCell")), KVariable("Rest")))),
                        KVariable("_2"),
                        KVariable("_3"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }
    @Test
    public void testFragment4() {
        K term = cell("<top>",cell("<t>",cell("<env>",KVariable("E")),KVariable("F")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")), KSequence(KVariable("F"), KVariable("Rest")))), KVariable("F2")));
        K expected = cell("<top>",app("_ThreadCellBag_",
                cell("<t>", KVariable("_0"), cell("<env>", KVariable("E")), KVariable("_1")),
                cell("<t>", cell("<k>", KRewrite(KSequence(KVariable("Rest")),
                                KSequence(cell("<t>-fragment", KVariable("_0"), app("noEnvCell"), KVariable("_1")), KVariable("Rest")))),
                        KVariable("_2"),
                        KVariable("_3"))));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    ConfigurationInfo bagCfgInfo = new TestConfiguration() {{
        addCell(null, "TopCell", "<top>");
        addCell("TopCell", "ThreadCell", "<t>", Multiplicity.STAR, Sorts.K());
        addCell("TopCell", "ExtraCell", "<extra>");
        addUnit("ThreadCell", KApply(KLabel(".ThreadCellBag")));
        addConcat("ThreadCell", KLabel("_ThreadCellBag_"));
    }};
    LabelInfo bagLabelInfo = new LabelInfo() {{
        addLabel("TopCell", "<top>");
        addLabel("ThreadCell", "<t>");
        addLabel("ExtraCell", "<extra>");
    }};
    @Test
    public void testFragmentBag() {
        K term = cell("<top>", KVariable("F"),cell("<t>", KRewrite(KVariable("Rest"),KSequence(KVariable("F"),KVariable("Rest")))));
        K expected = cell("<top>",
                app("_ThreadCellBag_", KVariable("_0"),
                        cell("<t>", KRewrite(KVariable("Rest"),
                                KSequence(app("<top>-fragment",KVariable("_0"),KVariable("_1")),KVariable("Rest"))))),
                KVariable("_1"));
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(expected, new SortCells(bagCfgInfo, bagLabelInfo, kem).sortCells(term));
        Assert.assertEquals(0, kem.getExceptions().size());
    }

    KApply app(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
