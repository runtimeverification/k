// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.junit.Rule;
import org.junit.rules.ExpectedException;
import org.kframework.compile.LabelInfo;
import org.kframework.kore.*;

import org.junit.Test;
import org.junit.Assert;

import static org.kframework.kore.KORE.*;

public class CloseCellsTest {

    final SortInfo sortInfo = new SortInfo() {{
        addOp("Map", "'_Map_");
        addOp("List", "'_List_");
    }};

    final TestConfiguration cfgInfo = new TestConfiguration() {{
        addCell(null, "ThreadCell", "<thread>", Multiplicity.STAR);
        addCell("ThreadCell", "KCell", "<k>", Sort("K"));
        addCell("ThreadCell", "EnvCell", "<env>", Sort("Map"));
        addCell(null, "ListCell", "<list>", Multiplicity.STAR, Sort("List"));
        addDefault("EnvCell", cell("<env>", KApply(KLabel(".Map"))));
        addDefault("KCell", cell("<k>",stringToToken("defaultK")));
    }};
    final LabelInfo labelInfo = new LabelInfo() {{
        addLabel("KCell", "<k>");
        addLabel("EnvCell", "<env>");
        addLabel("ThreadCell", "<thread>");
        addLabel("ListCell", "<list>");
        addLabel("Map", "'_Map_", true, true);
        addLabel("List", "'_List_", true);
    }};
    final ConcretizationInfo cfg = new ConcretizationInfo(cfgInfo, labelInfo);

    final static K dots = KApply(KLabel("#dots"));

    @Test
    public void testSimpleClosure() {
        K term = cell("<k>", KApply(KLabel("_+_"), KVariable("I"), KVariable("J")), dots);
        K expected = cell("<k>", KSequence(KApply(KLabel("_+_"), KVariable("I"), KVariable("J")),
                KVariable("DotVar0")));
        Assert.assertEquals(expected, new CloseTerm(cfg, sortInfo, labelInfo).close(term));
    }

    @Test
    public void testCloseMap() {
        K term = cell("<env>",dots,KApply(KLabel("'_|=>_"),intToToken(1),intToToken(2)));
        K expected = cell("<env>", KApply(KLabel("'_Map_"), KApply(KLabel("'_|=>_"), intToToken(1), intToToken(2)), KVariable("DotVar0")));
        Assert.assertEquals(expected, new CloseTerm(cfg, sortInfo, labelInfo).close(term));
    }

    @Test
    public void testCloseList() {
        K term = KApply(KLabel("#cells"),
                cell("<list>", dots, intToToken(1)),
                cell("<list>", intToToken(2), dots),
                cell("<list>", dots, intToToken(3), dots));
        K expected = KApply(KLabel("#cells"),
                cell("<list>", KApply(KLabel("'_List_"), KVariable("DotVar0"), intToToken(1))),
                cell("<list>", KApply(KLabel("'_List_"), intToToken(2), KVariable("DotVar1"))),
                cell("<list>", KApply(KLabel("'_List_"), KVariable("DotVar2"), KApply(KLabel("'_List_"), intToToken(3), KVariable("DotVar3")))));
        Assert.assertEquals(expected, new CloseTerm(cfg, sortInfo, labelInfo).close(term));
    }

    @Test
    public void testCloseCellVar() {
        K term = KApply(KLabel("#cells"),
                cell("<thread>",dots,cell("<k>", intToToken(1))),
                cell("<thread>",cell("<k>", intToToken(2)),dots),
                cell("<thread>",dots,cell("<k>", intToToken(2)),dots));
        K expected = KApply(KLabel("#cells"),
                cell("<thread>",cell("<k>",intToToken(1)),KVariable("DotVar0")),
                cell("<thread>",cell("<k>",intToToken(2)),KVariable("DotVar1")),
                cell("<thread>",cell("<k>",intToToken(2)),KVariable("DotVar2")));
        Assert.assertEquals(expected, new CloseTerm(cfg, sortInfo, labelInfo).close(term));
    }

    @Rule
    public ExpectedException exception = ExpectedException.none();

    @Test
    public void testClosedCellError1() {
        K term = cell("<thread>",cell("<k>"));
        exception.expect(IllegalArgumentException.class);
        exception.expectMessage("Closed parent cell missing required children [EnvCell] <thread>(<k>())");
        new CloseTerm(cfg, sortInfo, labelInfo).close(term);
    }

    @Test
    public void testCloseCellTerm() {
        K term = KRewrite(KApply(KLabel("#cells")),
                KApply(KLabel("#cells"),
                        cell("<thread>", dots, cell("<k>", intToToken(1))),
                        cell("<thread>", cell("<k>", intToToken(2)), dots),
                        cell("<thread>", dots, cell("<env>", intToToken(2)), dots)));
        K expected = KRewrite(KApply(KLabel("#cells")),
                KApply(KLabel("#cells"),
                cell("<thread>", cell("<k>", intToToken(1)), cell("<env>",KApply(KLabel(".Map")))),
                cell("<thread>", cell("<k>", intToToken(2)), cell("<env>",KApply(KLabel(".Map")))),
                cell("<thread>", cell("<env>", intToToken(2)), cell("<k>",stringToToken("defaultK")))));
        Assert.assertEquals(expected, new CloseTerm(cfg, sortInfo, labelInfo).close(term));
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
