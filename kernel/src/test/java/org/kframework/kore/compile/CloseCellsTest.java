// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.junit.Rule;
import org.junit.rules.ExpectedException;
import org.kframework.builtin.Sorts;
import org.kframework.compile.LabelInfo;
import org.kframework.kore.*;

import org.junit.Test;
import org.junit.Assert;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Arrays;

import static org.kframework.kore.KORE.*;

public class CloseCellsTest {

    final SortInfo sortInfo = new SortInfo() {{
        addOp("Map", "'_Map_");
        addOp("List", "'_List_");
    }};
    final TestConfiguration cfgInfo = new TestConfiguration() {{
        addCell(null, "ThreadCell", "<thread>", Multiplicity.STAR);
        addCell("ThreadCell", "KCell", "<k>", Sorts.K());
        addCell("ThreadCell", "EnvCell", "<env>", Sort("Map"));
        addCell(null, "ListCell", "<list>", Multiplicity.STAR, Sort("List"));
        addDefault("EnvCell", cell("<env>", KApply(KLabel(".Map"))));
        addDefault("KCell", cell("<k>", stringToToken("defaultK")));
    }};
    final LabelInfo labelInfo = new LabelInfo() {{
        addLabel("KCell", "<k>");
        addLabel("EnvCell", "<env>");
        addLabel("ThreadCell", "<thread>");
        addLabel("ListCell", "<list>");
        addLabel("Map", "'_Map_", true, true, true);
        addLabel("List", "'_List_", true, false, true);
    }};

    @Test
    public void testSimpleClosure() {
        K term = cell("<k>", false, true, KApply(KLabel("_+_"), KVariable("I"), KVariable("J")));
        K expected = ccell("<k>", KSequence(KApply(KLabel("_+_"), KVariable("I"), KVariable("J")),
                KVariable("DotVar0")));
        Assert.assertEquals(expected, new CloseCells(cfgInfo, sortInfo, labelInfo).close(term));
    }

    @Test
    public void testCloseMap() {
        K term = cell("<env>", true, false, KApply(KLabel("'_|=>_"), intToToken(1), intToToken(2)));
        K expected = ccell("<env>", KApply(KLabel("'_Map_"), KApply(KLabel("'_|=>_"), intToToken(1), intToToken(2)), KVariable("DotVar0")));
        Assert.assertEquals(expected, new CloseCells(cfgInfo, sortInfo, labelInfo).close(term));
    }

    @Test
    public void testCloseList() {
        K term = KApply(KLabel("#cells"),
                cell("<list>", true, false, intToToken(1)),
                cell("<list>", false, true, intToToken(2)),
                cell("<list>", true, true, intToToken(3)));
        K expected = KApply(KLabel("#cells"),
                ccell("<list>", KApply(KLabel("'_List_"), KVariable("DotVar0"), intToToken(1))),
                ccell("<list>", KApply(KLabel("'_List_"), intToToken(2), KVariable("DotVar1"))),
                ccell("<list>", KApply(KLabel("'_List_"), KVariable("DotVar2"), KApply(KLabel("'_List_"), intToToken(3), KVariable("DotVar3")))));
        Assert.assertEquals(expected, new CloseCells(cfgInfo, sortInfo, labelInfo).close(term));
    }

    @Test
    public void testCloseCellVar() {
        K term = KApply(KLabel("#cells"),
                cell("<thread>", true, false, cell("<k>", intToToken(1))),
                cell("<thread>", false, true, cell("<k>", intToToken(2))),
                cell("<thread>", true, true, cell("<k>", intToToken(2))));
        K expected = KApply(KLabel("#cells"),
                ccell("<thread>", ccell("<k>", intToToken(1)), KVariable("DotVar0")),
                ccell("<thread>", ccell("<k>", intToToken(2)), KVariable("DotVar1")),
                ccell("<thread>", ccell("<k>", intToToken(2)), KVariable("DotVar2")));
        Assert.assertEquals(expected, new CloseCells(cfgInfo, sortInfo, labelInfo).close(term));
    }

    @Rule
    public ExpectedException exception = ExpectedException.none();

    @Test
    public void testClosedCellError1() {
        K term = cell("<thread>", cell("<k>"));
        exception.expect(KEMException.class);
        exception.expectMessage("Closed parent cell missing required children [EnvCell]");
        new CloseCells(cfgInfo, sortInfo, labelInfo).close(term);
    }

    @Test
    public void testCloseCellTerm() {
        K term = KRewrite(cells(),
                  cells(cell("<thread>", true, false, cell("<k>", intToToken(1))),
                        cell("<thread>", false, true, cell("<k>", intToToken(2))),
                        cell("<thread>", true, true, cell("<env>", intToToken(2)))));
        K expected = KRewrite(cells(),
                  cells(ccell("<thread>", ccell("<k>", intToToken(1)), ccell("<env>", KApply(KLabel(".Map")))),
                        ccell("<thread>", ccell("<k>", intToToken(2)), ccell("<env>", KApply(KLabel(".Map")))),
                        ccell("<thread>", ccell("<env>", intToToken(2)), ccell("<k>", stringToToken("defaultK")))));
        Assert.assertEquals(expected, new CloseCells(cfgInfo, sortInfo, labelInfo).close(term));
    }

    KApply cell(String name, K... ks) {
        return cell(name, false, false, ks);
    }
    KApply cell(String name, boolean openLeft, boolean openRight, K... ks) {
        return IncompleteCellUtils.make(KLabel(name), openLeft, Arrays.asList(ks), openRight);
    }

    KApply ccell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }


    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
