// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.junit.Assert;
import org.junit.Test;
import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.kore.*;

import java.util.*;

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
        addCell("TopCell", "ThreadCell", "<t>");
        addCell("ThreadCell", "KCell", "<k>", Sort("K"));
        addCell("ThreadCell", "EnvCell", "<env>", Sort("Map"));
    }};
    LabelInfo labelInfo = new LabelInfo() {{
        addLabel("TopCell", "<top>");
        addLabel("ThreadCell", "<t>");
        addLabel("KCell", "<k>");
        addLabel("EnvCell", "<env>");
    }};

    @Test
    public void testSimpleSplitting() {
        K term = KRewrite(cell("<t>",cell("<env>"),KVariable("X")),KVariable("X"));
        K expected = KRewrite(cell("<t>",KVariable("X"),cell("<env>")),KVariable("X"));
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo).sortCells(term));
    }

    @Test
    public void testUselessVariable() {
        K term = cell("<t>",cell("<env>"),cell("<k>"),KVariable("X"));
        K expected = cell("<t>",cell("<k>"),cell("<env>"));
        Assert.assertEquals(expected, new SortCells(cfgInfo, labelInfo).sortCells(term));
    }

    KApply cell(String name, K... ks) {
        return KApply(KLabel(name), ks);
    }

    KApply cells(K... ks) {
        return KApply(KLabel("#cells"), ks);
    }
}
