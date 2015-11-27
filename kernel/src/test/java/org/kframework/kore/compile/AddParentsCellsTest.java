// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore.compile;


import com.google.common.collect.Lists;
import org.junit.Assert;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.kframework.builtin.KLabels;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.kil.Attribute;
import org.kframework.kore.*;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Arrays;

import static org.kframework.kore.KORE.*;
import static org.kframework.compile.ConfigurationInfo.Multiplicity.*;

public class AddParentsCellsTest {
    @Rule
    public final ExpectedException exception = ExpectedException.none();

    final ConfigurationInfo cfgInfo = new TestConfiguration() {{
        addCell(null, "TCell", "<T>");
        addCell("TCell", "TSCell", "<ts>");
        addCell("TCell", "StateCell", "<state>");
        addCell("TSCell", "tCell", "<t>", STAR);
        addCell("TSCell", "SchedulerCell", "<scheduler>");
        addCell("tCell", "KCell", "<k>");
        addCell("tCell", "EnvCell", "<env>");
        addCell("tCell", "MsgCell", "<msg>", STAR);
        addCell("MsgCell", "MsgIdCell", "<msgId>");
    }};
    final LabelInfo labelInfo = new LabelInfo() {{
        addLabel("TCell","<T>");
        addLabel("TSCell","<ts>");
        addLabel("tCell","<t>");
        addLabel("StateCell","<state>");
        addLabel("SchedulerCell","<scheduler>");
        addLabel("KCell","<k>");
        addLabel("EnvCell","<env>");
        addLabel("MsgCell","<msg>");
        addLabel("MsgIdCell","<msgId>");
    }};
    final AddParentCells pass = new AddParentCells(cfgInfo, labelInfo);

    @Test
    public void testOneLeafCellNoCompletion() {
        K term = cell("<k>", intToToken(2));
        K expected = cell("<k>", intToToken(2));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testTwoCellsNoCompletion() {
        K term = cell("<t>", cell("<k>", intToToken(2)));
        K expected = cell("<t>", cell("<k>", intToToken(2)));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testTwoCellsCompletion() {
        K term = cell("<ts>", cell("<k>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(2))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testMultiplicitySeparate() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", cell("<k>", intToToken(2))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testMultiplicityShared() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<env>", intToToken(2)));
        K expected = cell("<ts>", cell("<t>", cell("<k>", intToToken(1)), cell("<env>", intToToken(2))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test(expected = KEMException.class)
    public void testAmbiguityError() {
        K term = cell("<ts>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)), cell("<env>", intToToken(2)));
        pass.concretizeCell(term);
    }

    @Test
    public void testDeep2() {
        Assert.assertEquals(Lists.newArrayList(cell("<ts>", cell("<t>", intToToken(1)), cell("<t>", intToToken(2)))),
                pass.makeParents(KLabel("<ts>"), false, Lists.newArrayList(cell("<t>", intToToken(1)), cell("<t>", intToToken(2)))));
    }

    @Test
    public void testDeep() {
        K term = cell("<T>", cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<T>", cell("<ts>", cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", cell("<k>", intToToken(2)))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testRewrites() {
        K term = cell("<T>", cell("<k>", intToToken(1)), KRewrite(cell("<k>", intToToken(2)), cell("<k>")));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", KRewrite(cell("<k>", intToToken(2)), cell("<k>")))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testRewriteWithCells() {
        K term = cell("<T>", cell("<k>", intToToken(1)), KRewrite(cells(cell("<k>", intToToken(2)), cell("<msg>")), cell("<k>")));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", cell("<k>", intToToken(1))),
                cell("<t>", KRewrite(cells(cell("<k>", intToToken(2)), cell("<msg>")), cell("<k>")))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testRewriteWithCellVariable() {
        K term = cell("<T>", KRewrite(KVariable("KCell", Att().add(Attribute.SORT_KEY, "KCell")), cell("<k>", intToToken(1))));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", KRewrite(KVariable("KCell", Att().add(Attribute.SORT_KEY, "KCell")), cell("<k>", intToToken(1))))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testEmptySide() {
        K term = cell("<T>", cell("<k>"), KRewrite(cell("<msg>"), cells()));
        K expected = cell("<T>", cell("<ts>", cell("<t>", cell("<k>"), KRewrite(cell("<msg>"), cells()))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testTwoRewritesFit() {
        K term = cell("<T>", KRewrite(cells(), cell("<k>", intToToken(1))),
                KRewrite(cell("<k>", intToToken(2)), cells()));
        K expected = cell("<T>", cell("<ts>", cell("<t>",
                KRewrite(cells(), cell("<k>", intToToken(1))),
                KRewrite(cell("<k>", intToToken(2)), cells()))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testThreeRewritesSplit() {
        K term = cell("<T>",
                KRewrite(cells(cell("<k>"),cell("<env>")), cells()),
                KRewrite(cell("<env>"), cell("<k>")),
                KRewrite(cell("<k>"), cell("<k>")));
        K expected = cell("<T>", cell("<ts>",
                cell("<t>", KRewrite(cells(cell("<k>"),cell("<env>")), cells())),
                cell("<t>", KRewrite(cell("<env>"), cell("<k>"))),
                cell("<t>", KRewrite(cell("<k>"), cell("<k>")))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testDotsApart() {
        K term = cell("<T>", true, false, cell("<k>", intToToken(1)), cell("<k>", intToToken(2)));
        K expected = cell("<T>", true, true, cell("<ts>", true, true,
                cell("<t>", true, true, cell("<k>", intToToken(1))),
                cell("<t>", true, true, cell("<k>", intToToken(2)))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testDotsTogether() {
        K term = cell("<ts>", true, false, cell("<k>", intToToken(0)), cell("<env>",intToToken(2)));
        K expected = cell("<ts>", true, true, cell("<t>", true, true,
                cell("<k>", intToToken(0)), cell("<env>",intToToken(2))));
        Assert.assertEquals(expected, pass.concretizeCell(term));
    }

    @Test
    public void testNestedCompletion() {
        K term = cell("<T>",
                cell("<t>", cell("<msg>", intToToken(0)), cell("<msgId>", intToToken(1))),
                cell("<k>", intToToken(2)),
                cell("<env>", intToToken(3)),
                cell("<msgId>", intToToken(4)),
                cell("<msgId>", intToToken(5)),
                cell("<t>", cell("<k>", intToToken(6))));
        K expected = cell("<T>",cell("<ts>",
                cell("<t>", cell("<msg>", intToToken(0)), cell("<msg>", cell("<msgId>", intToToken(1)))),
                cell("<t>", cell("<k>", intToToken(6))),
                cell("<t>", cell("<k>", intToToken(2)), cell("<env>", intToToken(3)),
                    cell("<msg>", cell("<msgId>", intToToken(4))),
                    cell("<msg>", cell("<msgId>", intToToken(5))))
                ));
        Assert.assertEquals(expected, pass.concretize(term));

    }

    @Test
    public void testLeafContent() {
        K term = cell("<T>", cell("<k>",
                KSequence(KApply(KLabel("_+_"), KVariable("I"), KVariable("J")),
                        KVariable("Rest"))));
        K expected = cell("<T>", cell("<ts>", cell("<t>", cell("<k>",
                KSequence(KApply(KLabel("_+_"), KVariable("I"), KVariable("J")),
                        KVariable("Rest"))))));
        Assert.assertEquals(expected, pass.concretize(term));
    }

    @Test
    public void testNonCellItem() {
        K term = cell("<T>", KApply(KLabel(".K")), cell("<k>",KVariable("X")));
        K expected = cell("<T>",cells(KApply(KLabel(".K")), cell("<ts>", cell("<t>", cell("<k>", KVariable("X"))))));
        Assert.assertEquals(expected, pass.concretize(term));
    }

    @Test
    public void testNonCellItemRewrite() {
        K term = cell("<T>", KRewrite(KApply(KLabel("label")),cells(KApply(KLabel(".K")), cell("<k>",KVariable("X")))));
        exception.expect(KEMException.class);
        exception.expectMessage("Can't mix items with different parent cells under a rewrite");
        pass.concretize(term);
    }

    KApply cell(String name, K... ks) {
        return cell(name, false, false, ks);
    }
    KApply cell(String name, boolean openLeft, boolean openRight, K... ks) {
        return IncompleteCellUtils.make(KLabel(name), openLeft, Arrays.asList(ks), openRight);
    }

    KApply cells(K... ks) {
        return KApply(KLabel(KLabels.CELLS), ks);
    }
}
